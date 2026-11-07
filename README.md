# UnicornEmulationKiller
Built for LLVM 19.1 - Windows x64 <br> <br>

[Unicorn](https://github.com/unicorn-engine/unicorn) Is an emulator built on QEMU, It is frequently used in most symbolic execution backends and environment emulation backends. It is simply the standard for emulation backends<br>
Unlike WHP unicorn is mainly attacked through its featureset support, being an open source project it is mainly used for pipeline automation in anti malware systems, not for advanced research of obfuscated binaries. <br>
It is built on QEMU so it inherits all the failures of QEMU itself but with the vast amount of QEMU patches, its pretty easy to get the VM past most checks these days. <br>
Unlike WHP, QEMU isn't trying to get past as "Just another Hyper-V environment", it actually has to be hidden as it responds to erratas quite differently. <br>
This means the best form of attack isn't to the VM but to Unicorn's own hardware support. Back before AI Unicorn was FULL OF HOLES, but their contributors have really picked up pace in the past year. <br>


## The Attack

The main points of Unicorn's failure right now are:
* SHA-NI Support
* Some small x87 caveats(This has been greatly improved in the past year by Unicorn)
* WaitPKG
* GF-NI

We then do some other light anti VM stuff such as:
* RDTSC attestion
* CPUID aattestion
* XGETBV
<img width="1962" height="479" alt="image" src="https://github.com/user-attachments/assets/22d77381-3638-40da-942d-36756990b2c8" />
<img width="873" height="417" alt="image" src="https://github.com/user-attachments/assets/aa4ff012-8916-4a39-a294-57f367b3ad51" />

The anti VM stuff really wont help against anyone experienced with a proper QEMU set up, The Unicorn failures are universal though. They require major support changes to QEMU to counter. SHA-NI support has been requested since about 2019.
<br>

## Annotations
```c
__attribute__((annotate("unicornkill")))
``` 
* Applies protection to constants to prevent their emulation in unicorn environments

## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll
