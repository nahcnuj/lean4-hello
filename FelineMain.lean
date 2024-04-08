/--
`blockSize`はストリームから一度に読み取るバイト列の大きさである。
-/
def blockSize : USize := 20 * 1024 -- 20 KiB

/--
`dump`は(POSIX)ストリームを受け取り、「そのストリームから1ブロック（`block_size`）読み取ってその結果を標準出力に書き出す」ことをストリームの終わりまで繰り返すIOアクションである。

入力は再帰毎に小さくなるとは限らないので`partial`とマークする。
これによってLeanに停止性の証明を要求させないようにできる。
-/
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf : ByteArray ← stream.read blockSize
  if buf.isEmpty then /- do -/
    -- reached EOF
    pure ()
  else /- do -/
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream -- 末尾再帰

/--
`fileStream`はファイル名を受け取り、そのファイルが存在すればストリームを返し、存在しなければ`none`を返すIOアクションである。
-/
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none -- noneを返す
  else
    -- ファイルを読み取りモードで開く（ファイルハンドラを生成する）
    let handle : IO.FS.Handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    -- ファイルハンドラからStream構造体を生成する
    pure (some (IO.FS.Stream.ofHandle handle))
  -- ファイルハンドラが参照されなくなったらファイナライザがファイルディスクリプタを閉じる

/--
`process`は現在の終了コードと入力ファイルのリストを受け取り、`cat`コマンドと同様の動作をして終了コードを返すIOアクションである。

これは引数のリストが再帰毎に小さくなり、最後には空になって停止する。
ゆえに`partial`は不要。
-/
def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
    | []          => pure exitCode
    | "-" :: args => /- do -/
        -- 標準入力
        let stdin ← IO.getStdin
        dump stdin
        process exitCode args
    | filename :: args => /- do -/
        -- ファイル名
        let maybeStream ← fileStream ⟨filename⟩ -- (System.FilePath.mk filename)
        match maybeStream with
          | none =>
              process 1 args
          | some stream =>
              dump stream
              process exitCode args

def helpWanted : List String → Bool
  | [] => false
  | arg :: args => arg == "--help" || helpWanted args

/--
`feline`は`cat`コマンドと同様の働きをするコマンドである。
-/
def main (args : List String) : IO UInt32 := do
  if helpWanted args then
    let stdout ← IO.getStdout
    stdout.putStrLn "Usage: feline [--help] [FILE]..."
    pure 0
  else
    match args with
      | [] => process 0 ["-"] -- 引数がない場合は標準入力を受け付ける
      | _  => process 0 args
