import Ch1.Basic
import Ch1.Datatypes
import Ch1.Polymorphism
import Ch2.Feline
import Ch3.PropProof
import Ch4.PosTypeClasses
import Ch4.HttpHandlerExercise
import Ch4.OutParams
import Ch4.Indexing

#check zip -- in Chapter 1
#check process -- in Chapter 2
#check twoPlusThreeEqFive' -- in Chapter 3
#check fifteenMinusEightEqSeven'
#check (3 * 2 : Pos) --in Chapter 4
#check Handler.handle -- in Chapter 4


def testHttpHandler : IO Unit := do
  let aux_f := fun (base: System.FilePath) (chap: String) (fname: String)=> base.toString ++ "/" ++ chap ++ "/" ++ fname
  let cwd: System.FilePath ← IO.currentDir
  IO.println s!"Current working directory:{cwd}"
  let chapter := "Ch4"
  let index_uri := aux_f cwd chapter "index.html"
  let req : HttpRequest := { method := HttpMethod.get, uri := index_uri, version := "1.1" }
  let resp ← Handler.handle req
  IO.println resp.body

  let test_post_uri := aux_f cwd chapter "test-post.html"
  let req : HttpRequest := { method := HttpMethod.post, uri := test_post_uri, version := "1.1" }
  let resp ← Handler.handle req
  IO.println resp.body


  let test_post_uri := aux_f cwd chapter "test/"
  let req : HttpRequest := { method := HttpMethod.post, uri := test_post_uri, version := "1.1" }
  let resp ← Handler.handle req
  IO.println resp.body

  let test_delete_uri := aux_f cwd chapter "test-post.html"
  let req : HttpRequest := { method := HttpMethod.delete, uri := test_delete_uri, version := "1.1" }
  let resp ← Handler.handle req
  IO.println resp.body

  let test_delete_uri := aux_f cwd chapter "test/"
  let req : HttpRequest := { method := HttpMethod.delete, uri := test_delete_uri, version := "1.1" }
  let resp ← Handler.handle req
  IO.println resp.body

def testFeline (args: List String) : IO UInt32 := do
  let test_file ← IO.currentDir
  let test_file := test_file.toString ++ "/Ch2/test1.txt"
  match args with
  | [] => process 0 ["-"]
  | args =>
    match args.head! with
    | "-h" => do
      IO.println "Usage: cat [FILE]..."
      IO.println "-h\tDisplay this help message"
      IO.println s!"-d\tUse the default file name {test_file}"
      pure 0
    | "-d" => process 0 [test_file]
    | _ => process 0 args
    -- here is ok but leave the stream still open

    -- dump done solve the see the output

def main (args: List String) : IO Unit := do
  -- use default arg "-d"
  let ret ← testFeline args

  IO.println s!"Return code for testFeline: {ret}"

  testHttpHandler
