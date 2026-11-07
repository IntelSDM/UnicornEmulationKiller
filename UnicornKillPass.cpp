#include "UnicornKillPass.h"

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <functional>
#include <memory>
#include <random>
#include <string>
#include <vector>

using namespace llvm;

llvm::cl::opt<bool> UnicornKillEnable("obfunicornkill", llvm::cl::init(true), llvm::cl::desc("Master Toggle"));

static std::mt19937_64 UnicornRng((uint64_t)std::random_device{}() ^ (uint64_t)std::chrono::high_resolution_clock::now().time_since_epoch().count());

static constexpr unsigned PerFnCap = 256;
static constexpr unsigned MinBitwidth = 8;
static constexpr unsigned MaxBitwidth = 64;
static constexpr unsigned MaxSitesPerFn = 4;
static constexpr unsigned MinDomSubtree = 4;
static constexpr unsigned MaxPhiEdges = 2;
static constexpr unsigned DriftIterations = 100000;
static constexpr unsigned DriftThreshold = 10;

static GlobalVariable* ShaNiOk = nullptr;
static GlobalVariable* MovntpsFaulted = nullptr;
static GlobalVariable* DriftOk = nullptr;
static GlobalVariable* GfniOk = nullptr;
static GlobalVariable* WaitpkgOk = nullptr;

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga) return false;
    ConstantArray* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;
    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        ConstantStruct* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* strgv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!strgv || !strgv->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataSequential>(strgv->getInitializer());
        if (!cds || !cds->isString()) continue;
        if (strcmp(cds->getAsString().str().c_str(), tag) == 0) return true;
    }
    return false;
}

static bool HasUnicornKillAnnotation(Function& f)
{
    return HasAnnotationTag(f, "unicornkill");
}

static bool HasNoUnicornKillAnnotation(Function& f)
{
    return HasAnnotationTag(f, "nounicornkill");
}

struct Probe
{
    BasicBlock* Bb;
    uint64_t KBase;
    Value* KLive;
};

struct PhiEdgeCand
{
    BasicBlock* Pred;
    BasicBlock* Dest;
    PHINode* Phi;
    unsigned IncomingIdx;
    ConstantInt* Ci;
};

struct PhiEdgeBound
{
    BasicBlock* SplitBb;
    PHINode* Phi;
    unsigned IncomingIdx;
    ConstantInt* Ci;
};

static uint64_t Rand64(std::mt19937_64& local)
{
    return local();
}

static Value* EmitCpuid(IRBuilder<>& b, uint32_t leaf, uint32_t sub, const Twine& nm)
{
    LLVMContext& ctx = b.getContext();
    Type* i32 = Type::getInt32Ty(ctx);
    SmallVector<Type*, 4> tuplefields = {i32, i32, i32, i32};
    StructType* quadty = StructType::get(ctx, tuplefields);
    SmallVector<Type*, 2> asmargtys = {i32, i32};
    FunctionType* asmty = FunctionType::get(quadty, asmargtys, false);

    InlineAsm* ia = InlineAsm::get(asmty, "cpuid", "={ax},={bx},={cx},={dx},0,2,~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_ATT);
    SmallVector<Value*, 2> asmargs = {ConstantInt::get(i32, leaf), ConstantInt::get(i32, sub)};
    CallInst* ci = b.CreateCall(ia, asmargs, nm);
    ci->setDoesNotThrow();
    return ci;
}

static Value* EmitXgetbv(IRBuilder<>& b, uint32_t xcr, const Twine& nm)
{
    LLVMContext& ctx = b.getContext();
    Type* i32 = Type::getInt32Ty(ctx);
    SmallVector<Type*, 2> tuplefields = {i32, i32};
    StructType* pairty = StructType::get(ctx, tuplefields);
    FunctionType* asmty = FunctionType::get(pairty, {i32}, false);

    InlineAsm* ia = InlineAsm::get(asmty, "xgetbv", "={ax},={dx},{cx},~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_ATT);
    CallInst* ci = b.CreateCall(ia, {ConstantInt::get(i32, xcr)}, nm);
    ci->setDoesNotThrow();
    return ci;
}

static Value* EmitEqNormalize(IRBuilder<>& b, Value* d, const Twine& nm)
{
    Type* i64 = Type::getInt64Ty(b.getContext());
    Value* d64 = (d->getType()->isIntegerTy(64)) ? d : b.CreateZExt(d, i64, nm + "Z");
    Value* neg = b.CreateNeg(d64, nm + "Neg");
    Value* orc = b.CreateOr(d64, neg, nm + "Orc");
    Value* nz = b.CreateLShr(orc, ConstantInt::get(i64, 63), nm + "Nz");
    Value* eq = b.CreateXor(nz, ConstantInt::get(i64, 1), nm + "Eq");
    return b.CreateNeg(eq, nm + "Mask");
}

static Value* EmitNzNormalize(IRBuilder<>& b, Value* v, const Twine& nm)
{
    Type* i64 = Type::getInt64Ty(b.getContext());
    Value* v64 = (v->getType()->isIntegerTy(64)) ? v : b.CreateZExt(v, i64, nm + "Z");
    Value* neg = b.CreateNeg(v64, nm + "Neg");
    Value* orc = b.CreateOr(v64, neg, nm + "Orc");
    Value* msb = b.CreateLShr(orc, ConstantInt::get(i64, 63), nm + "Msb");
    return b.CreateNeg(msb, nm + "Mask");
}

static Value* EmitSigAvx(IRBuilder<>& b, Value* ecxl1)
{
    Value* bit = b.CreateAnd(ecxl1, b.getInt32(1u << 28), "UkAvxBit");
    return EmitNzNormalize(b, bit, "UkAvx");
}

static Value* EmitSigOsxsave(IRBuilder<>& b, Value* ecxl1)
{
    Value* bit = b.CreateAnd(ecxl1, b.getInt32(1u << 27), "UkOsxsaveBit");
    return EmitNzNormalize(b, bit, "UkOsxsave");
}

static Value* EmitSigAvx2(IRBuilder<>& b, Value* ebxl7)
{
    Value* bit = b.CreateAnd(ebxl7, b.getInt32(1u << 5), "UkAvx2Bit");
    return EmitNzNormalize(b, bit, "UkAvx2");
}

static Value* EmitSigXgetbv(IRBuilder<>& b)
{
    Value* pair = EmitXgetbv(b, 0u, "UkXgetbv");
    Value* eax = b.CreateExtractValue(pair, 0, "UkXgetbvEax");
    Value* low3 = b.CreateAnd(eax, b.getInt32(7u), "UkXgetbvLow3");
    Value* d = b.CreateXor(low3, b.getInt32(7u), "UkXgetbvD");
    return EmitEqNormalize(b, d, "UkXgetbv");
}

static Value* EmitSigLockNeg(IRBuilder<>& b, Function& f)
{
    LLVMContext& ctx = b.getContext();
    Type* i32 = Type::getInt32Ty(ctx);
    Type* i8 = Type::getInt8Ty(ctx);
    Type* ptrty = PointerType::getUnqual(ctx);

    IRBuilder<> ab(&f.getEntryBlock(), f.getEntryBlock().getFirstInsertionPt());
    AllocaInst* slot = ab.CreateAlloca(i32, nullptr, "UkLnSlot");
    slot->setAlignment(Align(4));

    StoreInst* st = b.CreateStore(ConstantInt::get(i32, 0x2363Au), slot);
    st->setVolatile(true);
    st->setAlignment(Align(4));

    FunctionType* asmty = FunctionType::get(i8, {ptrty}, false);
    InlineAsm* ia = InlineAsm::get(asmty, "lock negl ($1)\n\tsets $0", "=q,r,~{memory},~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_ATT);
    CallInst* ci = b.CreateCall(ia, {slot}, "UkLnSb");
    ci->setDoesNotThrow();

    Value* condz = b.CreateZExt(ci, i32, "UkLnCond");
    Value* d = b.CreateXor(condz, b.getInt32(1u), "UkLnD");
    return EmitEqNormalize(b, d, "UkLn");
}

static Value* EmitSigAdoxAdcx(IRBuilder<>& b)
{
    LLVMContext& ctx = b.getContext();
    Type* i64 = Type::getInt64Ty(ctx);

    FunctionType* asmty = FunctionType::get(i64, {}, false);
    InlineAsm* ia = InlineAsm::get(asmty,
        "xorq %rax, %rax\n\txorq %rbx, %rbx\n\txorq %rcx, %rcx\n\tstc\n\tadoxq %rbx, %rax\n\tadcxq %rax, %rcx\n\tmovq %rcx, $0",
        "=r,~{rax},~{rbx},~{rcx},~{cc},~{dirflag},~{fpsr},~{flags}",
        true, false, InlineAsm::AD_ATT);
    CallInst* ci = b.CreateCall(ia, {}, "UkAdxRcx");
    ci->setDoesNotThrow();

    Value* d = b.CreateXor(ci, ConstantInt::get(i64, 1ULL), "UkAdxD");
    return EmitEqNormalize(b, d, "UkAdx");
}

static Value* EmitSigFxsaveFip(IRBuilder<>& b, Function& f)
{
    LLVMContext& ctx = b.getContext();
    Type* i8 = Type::getInt8Ty(ctx);
    Type* i64 = Type::getInt64Ty(ctx);
    Type* ptrty = PointerType::getUnqual(ctx);

    IRBuilder<> ab(&f.getEntryBlock(), f.getEntryBlock().getFirstInsertionPt());
    ArrayType* bufty = ArrayType::get(i8, 512);
    AllocaInst* buf = ab.CreateAlloca(bufty, nullptr, "UkFxBuf");
    buf->setAlignment(Align(16));

    FunctionType* asmty = FunctionType::get(i64, {ptrty}, false);
    InlineAsm* ia = InlineAsm::get(asmty,
        "fninit\n\tfld1\n\t2: fsqrt\n\tfxsave64 ($1)\n\tfninit\n\tleaq 2b(%rip), $0\n\tmovq 8($1), %rcx\n\txorq %rcx, $0",
        "=&r,r,~{rcx},~{memory},~{st},~{st(1)},~{st(2)},~{st(3)},~{st(4)},~{st(5)},~{st(6)},~{st(7)},~{fpsr},~{dirflag},~{flags}",
        true, false, InlineAsm::AD_ATT);
    CallInst* ci = b.CreateCall(ia, {buf}, "UkFxD");
    ci->setDoesNotThrow();

    return EmitEqNormalize(b, ci, "UkFx");
}

static Value* EmitSigShaNi(IRBuilder<>& b)
{
    Type* i32 = Type::getInt32Ty(b.getContext());
    LoadInst* v = b.CreateLoad(i32, ShaNiOk, true, "UkShaNiV");
    v->setAlignment(Align(4));
    return EmitNzNormalize(b, v, "UkShaNi");
}

static Value* EmitSigMovntpsMisaligned(IRBuilder<>& b)
{
    Type* i32 = Type::getInt32Ty(b.getContext());
    LoadInst* v = b.CreateLoad(i32, MovntpsFaulted, true, "UkMovntpsV");
    v->setAlignment(Align(4));
    return EmitNzNormalize(b, v, "UkMovntps");
}

static Value* EmitSigTscDrift(IRBuilder<>& b)
{
    Type* i32 = Type::getInt32Ty(b.getContext());
    LoadInst* v = b.CreateLoad(i32, DriftOk, true, "UkDriftV");
    v->setAlignment(Align(4));
    return EmitNzNormalize(b, v, "UkDrift");
}

static Value* EmitSigGfni(IRBuilder<>& b)
{
    Type* i32 = Type::getInt32Ty(b.getContext());
    LoadInst* v = b.CreateLoad(i32, GfniOk, true, "UkGfniV");
    v->setAlignment(Align(4));
    return EmitNzNormalize(b, v, "UkGfni");
}

static Value* EmitSigWaitpkg(IRBuilder<>& b)
{
    Type* i32 = Type::getInt32Ty(b.getContext());
    LoadInst* v = b.CreateLoad(i32, WaitpkgOk, true, "UkWaitpkgV");
    v->setAlignment(Align(4));
    return EmitNzNormalize(b, v, "UkWaitpkg");
}

static void EmitExecProbeCtor(Module& m, StringRef ctorname, StringRef helpername, const char* asmtext, const char* asmconstraints, GlobalVariable* okglobal)
{
    LLVMContext& ctx = m.getContext();
    Type* i32 = Type::getInt32Ty(ctx);
    Type* voidty = Type::getVoidTy(ctx);
    PointerType* ptrty = PointerType::getUnqual(ctx);

    FunctionCallee seh = m.getOrInsertFunction("__C_specific_handler", FunctionType::get(i32, {}, true));
    Constant* sehc = cast<Constant>(seh.getCallee());

    FunctionType* voidft = FunctionType::get(voidty, {}, false);

    Function* helper = Function::Create(voidft, GlobalValue::InternalLinkage, helpername, &m);
    helper->addFnAttr(Attribute::NoInline);
    helper->addFnAttr(Attribute::OptimizeNone);
    {
        BasicBlock* bb = BasicBlock::Create(ctx, "Entry", helper);
        IRBuilder<> b(bb);
        InlineAsm* ia = InlineAsm::get(voidft, asmtext, asmconstraints, true, false, InlineAsm::AD_ATT);
        b.CreateCall(ia);
        b.CreateRetVoid();
    }

    Function* ctor = Function::Create(voidft, GlobalValue::InternalLinkage, ctorname, &m);
    ctor->setPersonalityFn(sehc);

    BasicBlock* entry = BasicBlock::Create(ctx, "Entry", ctor);
    BasicBlock* okbb = BasicBlock::Create(ctx, "Ok", ctor);
    BasicBlock* dispatch = BasicBlock::Create(ctx, "Dispatch", ctor);
    BasicBlock* handler = BasicBlock::Create(ctx, "Handler", ctor);
    BasicBlock* exitbb = BasicBlock::Create(ctx, "Exit", ctor);

    {
        IRBuilder<> b(entry);
        b.CreateInvoke(helper, okbb, dispatch);
    }
    {
        IRBuilder<> b(okbb);
        b.CreateStore(ConstantInt::get(i32, 1), okglobal);
        b.CreateBr(exitbb);
    }
    auto* cs = CatchSwitchInst::Create(ConstantTokenNone::get(ctx), nullptr, 1, (ctorname + "Cs").str(), dispatch);
    cs->addHandler(handler);
    {
        auto* cp = CatchPadInst::Create(cs, {ConstantPointerNull::get(ptrty)}, (ctorname + "Cp").str(), handler);
        CatchReturnInst::Create(cp, exitbb, handler);
    }
    {
        IRBuilder<> b(exitbb);
        b.CreateRetVoid();
    }

    appendToGlobalCtors(m, ctor, 65535);
}

static void EmitShaNiCtor(Module& m)
{
    LLVMContext& ctx = m.getContext();
    Type* i32 = Type::getInt32Ty(ctx);
    ShaNiOk = new GlobalVariable(m, i32, false, GlobalValue::InternalLinkage, ConstantInt::get(i32, 0), "UkShaNiOk");
    ShaNiOk->setAlignment(Align(4));
    EmitExecProbeCtor(m, "UkCtorShaNi", "UkDoShaNi", "sha1msg1 %xmm4, %xmm3", "~{xmm3},~{xmm4},~{dirflag},~{fpsr},~{flags}", ShaNiOk);
}

static void EmitMovntpsCtor(Module& m)
{
    LLVMContext& ctx = m.getContext();
    Type* i32 = Type::getInt32Ty(ctx);
    Type* i64 = Type::getInt64Ty(ctx);
    Type* i8 = Type::getInt8Ty(ctx);
    Type* voidty = Type::getVoidTy(ctx);
    PointerType* ptrty = PointerType::getUnqual(ctx);

    MovntpsFaulted = new GlobalVariable(m, i32, false, GlobalValue::InternalLinkage, ConstantInt::get(i32, 0), "UkMovntpsFaulted");
    MovntpsFaulted->setAlignment(Align(4));

    FunctionCallee seh = m.getOrInsertFunction("__C_specific_handler", FunctionType::get(i32, {}, true));
    Constant* sehc = cast<Constant>(seh.getCallee());
    FunctionType* voidft = FunctionType::get(voidty, {}, false);
    FunctionType* movft = FunctionType::get(voidty, {ptrty}, false);

    Function* movdo = Function::Create(movft, GlobalValue::InternalLinkage, "UkDoMovntps", &m);
    movdo->addFnAttr(Attribute::NoInline);
    movdo->addFnAttr(Attribute::OptimizeNone);
    {
        BasicBlock* bb = BasicBlock::Create(ctx, "Entry", movdo);
        IRBuilder<> b(bb);
        InlineAsm* ia = InlineAsm::get(movft, "movntps %xmm0, ($0)", "r,~{xmm0},~{memory},~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_ATT);
        b.CreateCall(ia, {movdo->getArg(0)});
        b.CreateRetVoid();
    }

    Function* ctormov = Function::Create(voidft, GlobalValue::InternalLinkage, "UkCtorMovntps", &m);
    ctormov->setPersonalityFn(sehc);
    {
        BasicBlock* entry = BasicBlock::Create(ctx, "Entry", ctormov);
        BasicBlock* okbb = BasicBlock::Create(ctx, "Ok", ctormov);
        BasicBlock* dispatch = BasicBlock::Create(ctx, "Dispatch", ctormov);
        BasicBlock* handler = BasicBlock::Create(ctx, "Handler", ctormov);
        BasicBlock* exitbb = BasicBlock::Create(ctx, "Exit", ctormov);

        ArrayType* bufty = ArrayType::get(i8, 32);
        {
            IRBuilder<> b(entry);
            AllocaInst* buf = b.CreateAlloca(bufty, nullptr, "UkMovBuf");
            buf->setAlignment(Align(16));
            Value* mis = b.CreateInBoundsGEP(bufty, buf, {ConstantInt::get(i64, 0), ConstantInt::get(i64, 1)}, "UkMovMis");
            b.CreateInvoke(movdo, okbb, dispatch, {mis});
        }
        {
            IRBuilder<> b(okbb);
            b.CreateBr(exitbb);
        }
        auto* cs = CatchSwitchInst::Create(ConstantTokenNone::get(ctx), nullptr, 1, "UkMovCs", dispatch);
        cs->addHandler(handler);
        {
            auto* cp = CatchPadInst::Create(cs, {ConstantPointerNull::get(ptrty)}, "UkMovCp", handler);
            auto* st = new StoreInst(ConstantInt::get(i32, 1), MovntpsFaulted, false, Align(4), handler);
            (void)st;
            CatchReturnInst::Create(cp, exitbb, handler);
        }
        {
            IRBuilder<> b(exitbb);
            b.CreateRetVoid();
        }
    }
    appendToGlobalCtors(m, ctormov, 65535);
}

static void EmitDriftCtor(Module& m)
{
    LLVMContext& ctx = m.getContext();
    Type* i32 = Type::getInt32Ty(ctx);
    Type* i64 = Type::getInt64Ty(ctx);
    Type* voidty = Type::getVoidTy(ctx);

    DriftOk = new GlobalVariable(m, i32, false, GlobalValue::InternalLinkage, ConstantInt::get(i32, 0), "UkDriftOk");
    DriftOk->setAlignment(Align(4));

    FunctionType* voidft = FunctionType::get(voidty, {}, false);
    Function* ctor = Function::Create(voidft, GlobalValue::InternalLinkage, "UkCtorDrift", &m);
    ctor->addFnAttr(Attribute::NoInline);
    ctor->addFnAttr(Attribute::OptimizeNone);

    BasicBlock* entry = BasicBlock::Create(ctx, "Entry", ctor);
    IRBuilder<> b(entry);

    SmallVector<Type*, 2> flds = {i64, i64};
    StructType* pair = StructType::get(ctx, flds);
    FunctionType* asmty = FunctionType::get(pair, {i32}, false);

    // scheduling or reg alloc around the two rdtscs would reorder the sampling and inflate delta on silicon; one opaque asm block prevents it
    InlineAsm* ia = InlineAsm::get(asmty,
        "rdtsc\n\tshlq $$32, %rdx\n\torq %rdx, %rax\n\tmovq %rax, $0\n\tmovl $2, %ecx\n\t1:\n\tnop\n\tdecl %ecx\n\tjnz 1b\n\trdtsc\n\tshlq $$32, %rdx\n\torq %rdx, %rax\n\tmovq %rax, $1",
        "=&r,=&r,r,~{rax},~{rcx},~{rdx},~{cc},~{memory},~{dirflag},~{fpsr},~{flags}",
        true, false, InlineAsm::AD_ATT);

    Value* itersc = ConstantInt::get(i32, (uint64_t)DriftIterations);
    CallInst* ci = b.CreateCall(ia, {itersc}, "UkDriftPair");
    ci->setDoesNotThrow();

    Value* s0 = b.CreateExtractValue(ci, 0, "UkDriftS0");
    Value* s1 = b.CreateExtractValue(ci, 1, "UkDriftS1");
    Value* delta = b.CreateSub(s1, s0, "UkDriftDelta");

    Value* itersi64 = b.CreateZExt(itersc, i64, "UkDriftIters64");
    Value* thresh = ConstantInt::get(i64, (uint64_t)DriftThreshold);
    Value* bound = b.CreateMul(itersi64, thresh, "UkDriftBound");
    Value* oki1 = b.CreateICmpULT(delta, bound, "UkDriftOk1");
    Value* oki32 = b.CreateZExt(oki1, i32, "UkDriftOkZ");
    auto* st = b.CreateStore(oki32, DriftOk);
    st->setAlignment(Align(4));
    b.CreateRetVoid();

    appendToGlobalCtors(m, ctor, 65535);
}

static void EmitGfniCtor(Module& m)
{
    LLVMContext& ctx = m.getContext();
    Type* i32 = Type::getInt32Ty(ctx);
    GfniOk = new GlobalVariable(m, i32, false, GlobalValue::InternalLinkage, ConstantInt::get(i32, 0), "UkGfniOk");
    GfniOk->setAlignment(Align(4));
    // bare "$0" is parsed as an llvm operand reference, so the gf2p8affineqb immediate must be written as "$$0" for literal 0 in gas at&t
    EmitExecProbeCtor(m, "UkCtorGfni", "UkDoGfni", "gf2p8affineqb $$0, %xmm4, %xmm3", "~{xmm3},~{xmm4},~{dirflag},~{fpsr},~{flags}", GfniOk);
}

static void EmitWaitpkgCtor(Module& m)
{
    LLVMContext& ctx = m.getContext();
    Type* i32 = Type::getInt32Ty(ctx);
    WaitpkgOk = new GlobalVariable(m, i32, false, GlobalValue::InternalLinkage, ConstantInt::get(i32, 0), "UkWaitpkgOk");
    WaitpkgOk->setAlignment(Align(4));
    EmitExecProbeCtor(m, "UkCtorWaitpkg", "UkDoWaitpkg", "umonitor %rsp", "~{dirflag},~{fpsr},~{flags}", WaitpkgOk);
}

static Value* EmitProbeAt(Function& f, Module& m, BasicBlock& probebb, uint64_t kbase)
{
    LLVMContext& ctx = m.getContext();
    Type* i64 = Type::getInt64Ty(ctx);

    IRBuilder<> b(&probebb, probebb.getFirstInsertionPt());

    Value* q1 = EmitCpuid(b, 0x00000001u, 0u, "UkCpuid1");
    Value* q70 = EmitCpuid(b, 0x00000007u, 0u, "UkCpuid7");

    Value* ecxl1 = b.CreateExtractValue(q1, 2, "UkC1Ecx");
    Value* ebxl70 = b.CreateExtractValue(q70, 1, "UkC7Ebx");

    Value* isamask = ConstantInt::get(i64, ~0ULL);
    auto andinto = [&](Value*& dst, Value* sig)
    {
        dst = b.CreateAnd(dst, sig, "UkAnd");
    };

    andinto(isamask, EmitSigAvx(b, ecxl1));
    andinto(isamask, EmitSigOsxsave(b, ecxl1));
    andinto(isamask, EmitSigAvx2(b, ebxl70));
    andinto(isamask, EmitSigXgetbv(b));

    Value* avxbit = b.CreateAnd(ecxl1, b.getInt32(1u << 28), "UkPgAvxBit");
    Value* hasavx = EmitNzNormalize(b, avxbit, "UkPgAvxHas");
    Value* bypassavx = b.CreateNot(hasavx, "UkPgAvxBypass");
    Value* isaeff = b.CreateOr(bypassavx, isamask, "UkIsaEff");

    Value* sigln = EmitSigLockNeg(b, f);

    Value* sigadx = EmitSigAdoxAdcx(b);
    Value* adxbit = b.CreateAnd(ebxl70, b.getInt32(1u << 19), "UkPgAdxBit");
    Value* hasadx = EmitNzNormalize(b, adxbit, "UkPgAdxHas");
    Value* bypassadx = b.CreateNot(hasadx, "UkPgAdxBypass");
    Value* adxeff = b.CreateOr(bypassadx, sigadx, "UkAdxEff");

    Value* sigfx = EmitSigFxsaveFip(b, f);

    Value* mask = isaeff;
    mask = b.CreateAnd(mask, sigln, "UkMLockNeg");
    mask = b.CreateAnd(mask, adxeff, "UkMAdx");
    mask = b.CreateAnd(mask, sigfx, "UkMFxsave");

    if (ShaNiOk) mask = b.CreateAnd(mask, EmitSigShaNi(b), "UkMShaNi");
    if (MovntpsFaulted) mask = b.CreateAnd(mask, EmitSigMovntpsMisaligned(b), "UkMMovntps");

    if (DriftOk) mask = b.CreateAnd(mask, EmitSigTscDrift(b), "UkMDrift");

    if (GfniOk) mask = b.CreateAnd(mask, EmitSigGfni(b), "UkMGfni");
    if (WaitpkgOk) mask = b.CreateAnd(mask, EmitSigWaitpkg(b), "UkMWaitpkg");

    Value* kbasec = ConstantInt::get(i64, kbase);
    Value* klive = b.CreateAnd(kbasec, mask, "UkK");

    return klive;
}

static SmallVector<BasicBlock*, 4> PickProbeSites(Function& f, DominatorTree& dt, unsigned cap, unsigned minsubtree)
{
    SmallVector<BasicBlock*, 4> picked;
    BasicBlock& entry = f.getEntryBlock();
    picked.push_back(&entry);
    if (cap <= 1) return picked;

    DenseMap<DomTreeNode*, unsigned> sizes;
    std::function<unsigned(DomTreeNode*)> compute = [&](DomTreeNode* n) -> unsigned
    {
        if (!n) return 0;
        auto it = sizes.find(n);
        if (it != sizes.end()) return it->second;
        unsigned s = 1;
        for (DomTreeNode* c : *n) s += compute(c);
        sizes[n] = s;
        return s;
    };
    compute(dt.getRootNode());

    struct Cand
    {
        BasicBlock* Bb;
        unsigned Size;
    };
    SmallVector<Cand, 16> cands;
    for (BasicBlock& bb : f)
    {
        if (&bb == &entry) continue;
        if (bb.isEHPad()) continue;
        if (bb.getFirstInsertionPt() == bb.end()) continue;
        DomTreeNode* n = dt.getNode(&bb);
        if (!n) continue;
        unsigned sz = sizes.lookup(n);
        if (sz < minsubtree) continue;
        cands.push_back({&bb, sz});
    }

    std::sort(cands.begin(), cands.end(), [](const Cand& a, const Cand& b) { return a.Size > b.Size; });

    for (const Cand& c : cands)
    {
        if (picked.size() >= cap) break;
        picked.push_back(c.Bb);
    }
    return picked;
}

static SmallVector<PhiEdgeCand, 4> CollectPhiEdgeCands(Function& f, unsigned minbw, unsigned maxbw, unsigned cap)
{
    SmallVector<PhiEdgeCand, 4> cands;
    if (cap == 0) return cands;

    for (BasicBlock& dest : f)
    {
        if (pred_size(&dest) < 2) continue;
        for (PHINode& phi : dest.phis())
        {
            Type* phity = phi.getType();
            if (!phity->isIntegerTy()) continue;
            unsigned bw = phity->getIntegerBitWidth();
            if (bw < minbw) continue;
            if (bw > maxbw) continue;
            if (bw == 1) continue;
            for (unsigned i = 0; i < phi.getNumIncomingValues(); ++i)
            {
                auto* ci = dyn_cast<ConstantInt>(phi.getIncomingValue(i));
                if (!ci) continue;
                BasicBlock* pred = phi.getIncomingBlock(i);
                if (succ_size(pred) < 2) continue;
                cands.push_back({pred, &dest, &phi, i, ci});
                if (cands.size() >= cap) return cands;
            }
            if (cands.size() >= cap) return cands;
        }
    }
    return cands;
}

static size_t FindProbeIdxFor(DominatorTree& dt, const DenseMap<BasicBlock*, size_t>& idxmap, BasicBlock* bb)
{
    for (DomTreeNode* n = dt.getNode(bb); n; n = n->getIDom())
    {
        auto it = idxmap.find(n->getBlock());
        if (it != idxmap.end()) return it->second;
    }
    return 0;
}

static void RewriteOperand(Instruction& i, unsigned opidx, ConstantInt* ci, Value* klive64, uint64_t kbase)
{
    LLVMContext& ctx = i.getContext();
    unsigned bw = ci->getBitWidth();
    IntegerType* iwty = IntegerType::get(ctx, bw);

    uint64_t plain = ci->getZExtValue();
    uint64_t mask = (bw == 64) ? ~0ULL : ((1ULL << bw) - 1ULL);
    uint64_t kw = kbase & mask;
    uint64_t kct = (plain ^ kw) & mask;

    IRBuilder<> ub(&i);
    Value* kslice = klive64;
    if (bw != 64) kslice = ub.CreateTrunc(klive64, iwty, "UkKTr");
    Value* kctv = ConstantInt::get(iwty, kct);
    Value* dec = ub.CreateXor(kctv, kslice, "UkC");
    i.setOperand(opidx, dec);
}

static void RewritePhiEdgeOperand(PHINode* phi, unsigned incomingidx, ConstantInt* ci, BasicBlock* splitbb, Value* klive64, uint64_t kbase)
{
    LLVMContext& ctx = phi->getContext();
    unsigned bw = ci->getBitWidth();
    IntegerType* iwty = IntegerType::get(ctx, bw);

    uint64_t plain = ci->getZExtValue();
    uint64_t mask = (bw == 64) ? ~0ULL : ((1ULL << bw) - 1ULL);
    uint64_t kw = kbase & mask;
    uint64_t kct = (plain ^ kw) & mask;

    IRBuilder<> ub(splitbb->getTerminator());
    Value* kslice = klive64;
    if (bw != 64) kslice = ub.CreateTrunc(klive64, iwty, "UkKTr");
    Value* kctv = ConstantInt::get(iwty, kct);
    Value* dec = ub.CreateXor(kctv, kslice, "UkCPhi");
    phi->setIncomingValue(incomingidx, dec);
}

static bool ProcessFunction(Function& f, ArrayRef<Probe> probes, const DenseSet<BasicBlock*>& edgeprobebbs, DominatorTree& dt, LoopInfo* li)
{
    DenseMap<BasicBlock*, size_t> probeidxmap;
    DenseSet<BasicBlock*> probesitebbs;
    for (size_t i = 0; i < probes.size(); ++i)
    {
        probeidxmap[probes[i].Bb] = i;
        probesitebbs.insert(probes[i].Bb);
    }

    DenseSet<BasicBlock*> covered;
    unsigned uses = 0;

    for (BasicBlock& bb : f)
    {
        if (probesitebbs.count(&bb) || edgeprobebbs.count(&bb)) continue;
        if (li)
        {
            if (Loop* l = li->getLoopFor(&bb))
            {
                if (l->getHeader() == &bb) continue;
            }
        }

        size_t probeidx = FindProbeIdxFor(dt, probeidxmap, &bb);
        const Probe& p = probes[probeidx];

        for (Instruction& i : bb)
        {
            if (uses >= PerFnCap) break;

            if (isa<IntrinsicInst>(&i)) continue;
            if (isa<PHINode>(&i)) continue;
            if (isa<SwitchInst>(&i)) continue;

            CallBase* cb = dyn_cast<CallBase>(&i);
            unsigned calledidx = cb ? cb->getCalledOperandUse().getOperandNo() : ~0u;

            GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(&i);
            DenseSet<unsigned> gepstructslots;
            if (gep)
            {
                unsigned opno = 1;
                for (auto it = gep_type_begin(gep), end = gep_type_end(gep); it != end; ++it, ++opno)
                {
                    if (it.isStruct()) gepstructslots.insert(opno);
                }
            }

            for (unsigned o = 0; o < i.getNumOperands(); ++o)
            {
                if (cb && o == calledidx) continue;
                if (gep && gepstructslots.count(o)) continue;

                auto* ci = dyn_cast<ConstantInt>(i.getOperand(o));
                if (!ci) continue;

                unsigned bw = ci->getBitWidth();
                if (bw < MinBitwidth) continue;
                if (bw > MaxBitwidth) continue;
                if (bw == 1) continue;

                RewriteOperand(i, o, ci, p.KLive, p.KBase);
                covered.insert(&bb);
                ++uses;
                if (uses >= PerFnCap) break;
            }
            if (uses >= PerFnCap) break;
        }
    }

    return uses > 0;
}

bool RunUnicornKill(Module& m)
{
    if (!UnicornKillEnable) return false;

    uint64_t seed = ((uint64_t)UnicornRng() << 32) | (uint64_t)UnicornRng();
    std::mt19937_64 local(seed);

    ShaNiOk = nullptr;
    MovntpsFaulted = nullptr;
    DriftOk = nullptr;
    GfniOk = nullptr;
    WaitpkgOk = nullptr;

    bool changed = false;

    bool anyannotated = false;
    for (Function& f : m)
    {
        if (f.isDeclaration() || f.empty()) continue;
        if (!HasUnicornKillAnnotation(f)) continue;
        if (HasNoUnicornKillAnnotation(f)) continue;
        anyannotated = true;
        break;
    }
    if (anyannotated)
    {
        EmitShaNiCtor(m);
        EmitMovntpsCtor(m);
        EmitDriftCtor(m);
        EmitGfniCtor(m);
        EmitWaitpkgCtor(m);
    }

    for (Function& f : m)
    {
        if (f.isDeclaration() || f.empty()) continue;
        if (!HasUnicornKillAnnotation(f)) continue;
        if (HasNoUnicornKillAnnotation(f)) continue;

        SmallVector<PhiEdgeCand, 4> phicands = CollectPhiEdgeCands(f, MinBitwidth, MaxBitwidth, MaxPhiEdges);

        SmallVector<PhiEdgeBound, 4> phibindings;
        if (!phicands.empty())
        {
            CriticalEdgeSplittingOptions opts;
            for (const PhiEdgeCand& c : phicands)
            {
                BasicBlock* splitbb = SplitCriticalEdge(c.Pred, c.Dest, opts);
                if (!splitbb) continue;
                phibindings.push_back({splitbb, c.Phi, c.IncomingIdx, c.Ci});
            }
        }

        DominatorTree dt;
        dt.recalculate(f);
        std::unique_ptr<LoopInfo> li(new LoopInfo());
        li->analyze(dt);

        SmallVector<BasicBlock*, 4> sites = PickProbeSites(f, dt, MaxSitesPerFn, MinDomSubtree);

        SmallVector<Probe, 4> probes;
        probes.reserve(sites.size() + phibindings.size());
        for (BasicBlock* site : sites)
        {
            uint64_t kbase = 0;
            while (kbase == 0) kbase = Rand64(local);
            Value* klive = EmitProbeAt(f, m, *site, kbase);
            probes.push_back({site, kbase, klive});
        }

        DenseSet<BasicBlock*> edgeprobebbs;
        for (const PhiEdgeBound& bnd : phibindings)
        {
            uint64_t kbase = 0;
            while (kbase == 0) kbase = Rand64(local);
            Value* klive = EmitProbeAt(f, m, *bnd.SplitBb, kbase);
            edgeprobebbs.insert(bnd.SplitBb);
            RewritePhiEdgeOperand(bnd.Phi, bnd.IncomingIdx, bnd.Ci, bnd.SplitBb, klive, kbase);
        }

        bool fnchanged = ProcessFunction(f, probes, edgeprobebbs, dt, li.get());

        if (fnchanged || !probes.empty()) changed = true;
    }

    return changed;
}

PreservedAnalyses UnicornKillPass::run(Module& m, ModuleAnalysisManager&)
{
    bool changed = RunUnicornKill(m);
    return changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}