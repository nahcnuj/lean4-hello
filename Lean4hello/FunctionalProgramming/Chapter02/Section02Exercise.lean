/--
1. evaluate `IO.println "Hello!"`; returned an IO Unit value(action), which is associated with `englishGreeting` because of `:=`
2. evaluate `IO.println "Bonjour!"`; returned an IO Unit value(action); executed the IO action; printed `Bonjour!`
3. evaluate `englishGreeting`; executed the associated IO action; printed `Hello!`

Check:
```
PS C:\Users\user\work\lean4hello> lean --run .\Lean4hello\FunctionalProgramming\Chapter02\Section02Exercise.lean
Bonjour!
Hello!
PS C:\Users\user\work\lean4hello>
```
-/
def main : IO Unit := do
  let englishGreeting /- : IO Unit -/ := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting
