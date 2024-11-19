-- read buffer size each time
def bufsize : USize := 20 * 1024

partial def dump (stream: IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize-- need a USize para
  if buf.isEmpty then
    pure ()
  else
    let stdout <- IO.getStdout
    stdout.write buf
    dump stream -- may not terminate


-- add Option
def fileStream? (fileName: System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← fileName.pathExists
  if not fileExists then
    let stderr <- IO.getStderr
    stderr.putStr s!"File not found: {fileName}"
    -- pure () --match to IO Unit but I need to pattern match IO Stream
    -- pure (none)
    IO.getStdin
  else -- fileExists === Bool.true
    let handle <- IO.FS.Handle.mk fileName IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))


def fileStream! (fileName: System.FilePath) : IO (IO.FS.Stream) := do
  let fileExists ← fileName.pathExists
  if not fileExists then
    let stderr <- IO.getStderr
    stderr.putStr s!"File not found: {fileName}. Panic!"
    -- pure () --match to IO Unit but I need to pattern match IO Stream
    panic! "fileStream! broken"

  else -- fileExists === Bool.true
    let stdout <- IO.getStdout
    stdout.putStr s!"File found: {fileName}"
    -- pure (some (IO.getStdin)) -- BaseIO IO.FS.Stream : Type missmatch IO.FS.Stream
    -- let handle <- IO.FS.Handle.mk fileName IO.FS.Mode.readWrite
    let handle <- IO.FS.Handle.mk fileName IO.FS.Mode.read
    println! s!"File found: {fileName}"
    pure (IO.FS.Stream.ofHandle handle)


def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin <- IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    -- let stream <- fileStream! filename
    -- dump stream
    -- process exitCode args
    let stream <- fileStream? filename
    match stream with
    | none => process 1 args
    | some stream => do
      dump stream
      process exitCode args

def onePlusOneIsTwo : 1 + 1 = 2 := rfl
def onePlusOneIsTwo' : Prop := 1 + 1 = 2
theorem onePlusOneIsTwo'' : 1 + 1 = 2 := by
  simp
#check (onePlusOneIsTwo' : Prop)
-- #check (onePlusOneIsTwo : Prop) --error type mismatch
