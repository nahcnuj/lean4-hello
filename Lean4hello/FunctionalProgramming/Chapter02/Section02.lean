/--
`twice`はIOアクションを引数に取り、それを2回実行する新しいアクションを返す
-/
def twice (action : IO Unit) : IO Unit := do
  action
  action

/--
`nTimes`はIOアクションを引数に取り、自然数`n`を受け取ってアクションを`n`回実行する新しいアクションを返す
-/
def nTimes (action : IO Unit) : Nat → IO Unit
  | Nat.zero   => pure () -- `pure`は「副作用なしに引数の値を返す」IOアクション
  | Nat.succ n => do
      action          -- 1回`action`を実行して
      nTimes action n -- 再帰呼び出しの結果を実行する

/--
`countDown`は自然数`n`を受け取って、*未*実行のIOアクションのリストを返す
この関数は副作用を持たない（IOアクションではない）。何も出力しない
-/
def countDown : Nat → List (IO Unit)
  | Nat.zero   => [IO.println "Go!"]
  | Nat.succ n => IO.println s!"{Nat.succ n}" :: countDown n

example : countDown 0 = [IO.println "Go!"] := rfl
example : countDown 1 = [IO.println "1", IO.println "Go!"] := rfl
example : countDown 3 = [IO.println "3", IO.println "2", IO.println "1", IO.println "Go!"] := rfl

/--
`runActions`はIOアクションのリストを受け取って、順番にすべて実行するIOアクションを返す
-/
def runActions : List (IO Unit) → IO Unit
  | []             => pure () -- 「何もせず`() : Unit`を返す」アクション
  | act :: actions => do      -- 「先頭のアクションを実行して残りのアクションを再帰的に実行する」アクション
      act
      runActions actions

def from5 : List (IO Unit) := countDown 5
example : from5.length = 6 := rfl

/--
実行結果：
```
PS C:\Users\user\work\lean4hello> lean --run .\Lean4hello\FunctionalProgramming\Chapter02\Section02.lean
5
4
3
2
1
Go!
PS C:\Users\user\work\lean4hello>
```
-/
def main : IO Unit := runActions from5
