/--
実行例：
```
PS C:\Users\user\work\lean4hello> lean --run .\Lean4hello\FunctionalProgramming\Chapter02\HelloName.lean
Enter your name: jun
Hello, jun!
PS C:\Users\user\work\lean4hello>
```
-/
def main : IO Unit := do -- IOアクションの列を書けるように
  let stdin ← IO.getStdin   -- `←`でIOアクションの結果をローカル変数に保存する
  -- 1. `←`の右の式`IO.getStdin`を評価(evaluate)する：`IO.getStdin`はただの変数だからその値が検索され、それはビルトインのプリミティブなIOアクションである
  -- 2. IOアクションを実行(execute)する：`IO.FS.Stream`型の標準入力ストリームを表す値をもたらす
  -- 3. 実行結果が`←`の左の名前`stdin`に関連付けられる

  let stdout ← IO.getStdout -- stdin/stdoutをプログラムの中で局所的にオーバーライドできる
  -- 同様に、式の評価・IOアクションの実行・関連付けがなされる


  stdout.putStr "Enter your name: "
  -- IO.FS.Stream.putStr : IO.FS.Stream → String → IO Unit
  -- ストリームと文字列を受け取ってIOアクションを返す関数
  -- 式を評価してIOアクション、それが実行されて標準出力へ文字列が書き込まれる
  -- この文は式だけでできているので新しい変数は導入されない

  let input : String <- stdin.getLine
  -- IO.FS.Stream.getLine : IO.FS.Stream → IO String
  -- ストリームを受け取って、文字列を返すIOアクションを返す
  -- アクションを実行すると1行入力されるのを待ち、入力された行（例えば`"David\n"`）が`input`に関連付けられる

  let name  : String := input.dropRightWhile Char.isWhitespace
  -- String.dropRightWhile : String → String
  -- IOアクションではなく普通の関数なので`:=`を使う
  -- アクションではないので評価された後「実行」はされない


  stdout.putStrLn s!"Hello, {name}!"
  -- IO.FS.Stream.putStrLn : IO.FS.Stream → String → IO Unit
