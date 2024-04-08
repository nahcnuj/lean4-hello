# Hello, Lean 4

- [Theorem Proving in Lean 4 日本語訳](https://aconite-ac.github.io/theorem_proving_in_lean4_ja/title_page.html)
- [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/title.html)

## Initialization

- https://github.com/leanprover/elan
- https://lean-lang.org/lean4/doc/setup.html

```ps1
curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
del elan-init.ps1

elan self update
```

Build and run:

```
PS C:\Users\user\work\lean4hello> lake build
[1/6] Compiling Lean4hello.Basic
[2/6] Compiling Lean4hello
[2/6] Building Main
[3/6] Compiling Main
[6/6] Linking lean4hello.exe
PS C:\Users\user\work\lean4hello> lake exe lean4hello
Hello, world!
```

[Feline](https://leanprover.github.io/functional_programming_in_lean/hello-world/cat.html):

```
PS C:\Users\user\work\lean4hello> lake build feline
[0/2] Building FelineMain
[1/2] Compiling FelineMain
[2/2] Linking feline.exe
PS C:\Users\user\work\lean4hello> echo "It works!" | lake exe feline
It works!
PS C:\Users\user\work\lean4hello>
```
