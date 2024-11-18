inductive HttpMethod where
  | get
  | post
  | put
  | delete
deriving Repr

def httpMethodToString : HttpMethod → String
  | HttpMethod.get => "GET"
  | HttpMethod.post => "POST"
  | HttpMethod.put => "PUT"
  | HttpMethod.delete => "DELETE"

instance : ToString HttpMethod where
  toString := httpMethodToString

structure HttpRequest where
  method: HttpMethod
  uri: String
  version: String
deriving Repr

structure HttpResponse where
  status: UInt32
  body: String

instance : ToString HttpResponse where
  toString res := s!"[HttpResponse] Status: {res.status}, Body: {res.body}"



class Handler  (α: Type) where
  handle: α → IO HttpResponse

inductive UriType where
  | file (s : String)
  | dir

def uriCheck (uri: String): Option UriType :=
  if uri.endsWith ".html" then
    match (uri.splitOn "/").getLast? with
    | some file => some (UriType.file file)
    | none => none
  else if uri.endsWith "/" then
    some UriType.dir
  else
    none
def handleRequest (req: HttpRequest): IO HttpResponse :=
  if let none := uriCheck req.uri then
    pure { status := 404, body := "Not Found" : HttpResponse }
  else
    let file_name := match uriCheck req.uri with
    | some (UriType.file file) => some file
    | _ => none

    match req.method with
    | HttpMethod.get => do
      IO.println s!"Processing GET request for {req.uri}"
      if let none := file_name then
        pure {status := 200, body := "URI is a directory" : HttpResponse }
      else
      let page ← IO.FS.readFile req.uri
      pure { status := 200, body := page  : HttpResponse }
    | HttpMethod.post => do
      IO.println s!"Processing POST request for {req.uri}"
      if let some f := file_name then
        -- let s := (req.uri.splitOn "/").dropLast.drop 1
        -- IO.println s
        -- let dir := s.foldl (λ acc x => acc ++ "/" ++ x) ""
        -- IO.println dir
        -- IO.println f

        -- -- if need split dir and filename

        IO.FS.writeFile (req.uri : System.FilePath) f

      else
        IO.FS.createDir (req.uri: System.FilePath)
      pure { status := 201, body := s!"Created {req.uri}, handle POST." : HttpResponse }
    | HttpMethod.put => do
      IO.println s!"Processing PUT request for {req.uri}"
      pure { status := 204, body := s!"Created {req.uri}, handle PUT." : HttpResponse }
    | HttpMethod.delete => do
      let file_name := match uriCheck req.uri with
        | some (UriType.file file) => some file
        | _ => none
      IO.println s!"Processing DELETE request for {req.uri}"
      if let some _ := file_name then
        IO.FS.removeFile (req.uri: System.FilePath)
      else
        IO.FS.removeDir (req.uri: System.FilePath)
      pure { status := 204, body := s!"Deleted {req.uri}, handle DELETE." : HttpResponse }


instance : Handler HttpRequest where
  handle := handleRequest


#eval do
  let cwd: System.FilePath ← IO.currentDir
  IO.println s!"Current working directory:{cwd}"
  let chapter := "/ch4"
  let index_uri := cwd.toString ++ chapter ++ "/index.html"
  let req : HttpRequest := { method := HttpMethod.get, uri := index_uri, version := "1.1" }
  let resp ← Handler.handle req
  IO.println resp.body

  let test_post_uri := cwd.toString ++ chapter ++ "/test-post.html"
  let req : HttpRequest := { method := HttpMethod.post, uri := test_post_uri, version := "1.1" }
  let resp ← Handler.handle req
  IO.println resp.body


  let test_post_uri := cwd.toString ++ chapter ++ "/test/"
  let req : HttpRequest := { method := HttpMethod.post, uri := test_post_uri, version := "1.1" }
  let resp ← Handler.handle req
  IO.println resp.body

  let test_delete_uri := cwd.toString ++ chapter ++ "/test-post.html"
  let req : HttpRequest := { method := HttpMethod.delete, uri := test_delete_uri, version := "1.1" }
  let resp ← Handler.handle req
  IO.println resp.body

  let test_delete_uri := cwd.toString ++ chapter ++ "/test/"
  let req : HttpRequest := { method := HttpMethod.delete, uri := test_delete_uri, version := "1.1" }
  let resp ← Handler.handle req
  IO.println resp.body



-- def processRequest (req: HttpRequest): IO HttpResponse :=
--   match req.method with
--   | HttpMethod.get => do

--   | HttpMethod.post => do
--     IO.println s!"Processing POST request for {req.uri}"
--     IO.FS.createDir (req.uri: System.FilePath)
--     if
--   | HttpMethod.put => do
--     IO.println s!"Processing PUT request for {req.uri}"
--     pure 204
--   | HttpMethod.delete => do
--     IO.println s!"Processing DELETE request for {req.uri}"
--     pure 204
