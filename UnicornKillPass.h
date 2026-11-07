#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct UnicornKillPass : llvm::PassInfoMixin<UnicornKillPass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunUnicornKill(llvm::Module& m);

extern llvm::cl::opt<bool> UnicornKillEnable;