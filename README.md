# Hello, Lean 4

- [Theorem Proving in Lean 4 日本語訳](https://aconite-ac.github.io/theorem_proving_in_lean4_ja/title_page.html)

## Initialization

- https://github.com/leanprover/elan
- https://lean-lang.org/lean4/doc/setup.html

```ps1
curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
del elan-init.ps1

elan self update
elan toolchain install leanprover/lean4:4.6.1
```

Build and run:

```
PS C:\Users\user\work\lean4hello> lake build
[1/6] Compiling Lean4hello.Basic
[2/6] Compiling Lean4hello
[2/6] Building Main
[3/6] Compiling Main
[6/6] Linking lean4hello.exe
PS C:\Users\user\work\lean4hello> .\.lake\build\bin\lean4hello.exe     
Hello, world!
```
