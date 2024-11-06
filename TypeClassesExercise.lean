structure Pos where
  succ ::
  pred : Nat
deriving Repr

def one' := Pos.succ 0
def two' := Pos.succ 1
def three' := Pos.succ 2

def posAdd (x y : Pos) : Pos :=
  Pos.succ (x.pred + y.pred + 1)
def posAdd' : Pos → Pos → Pos :=
  fun x y =>
  match x, y with
  | Pos.succ x', Pos.succ y' =>Pos.succ (x' + y' + 1)

-- both posAdd and posAdd' are correct
-- Pos in pred version
instance : Add Pos where
  add := posAdd
def five' := two' + three'
#eval five'

def posMul (x y : Pos) : Pos :=
  Pos.succ (x.pred * y.pred + x.pred + y.pred)
def posMul' : Pos → Pos → Pos :=
  fun x y =>
  match x, y with
  | Pos.succ x', Pos.succ y' => Pos.succ (x' * y' + x' + y')
def posMul'' : Pos → Pos → Pos
  | Pos.succ x', Pos.succ y' => Pos.succ (x' * y' + x' + y')
instance : Mul Pos where
  mul := posMul
#eval three' * three'

def posToString : Pos → String
  | Pos.succ x => s!"{x+1}"
instance : ToString Pos where
  toString := posToString
#eval s!"{three'}"
#eval s!"{three' * three'}"

instance : OfNat Pos (n + 1) where
  ofNat := Pos.succ n
def five'': Pos := 5
theorem five'_eq_five'' : five' = five'' := by rfl
#print five'_eq_five''

-- Even
inductive Even where
  | zero
  | next (n : Even)

def evenAdd : Even → Even → Even
  | Even.zero, y => y
  | Even.next x', y => Even.next (evenAdd x' y)

def evenMul : Even → Even → Even
  | Even.zero, _ => Even.zero
  | Even.next x', y => evenAdd (evenMul x' y) (evenAdd y y)

-- def toString (atTop : Bool) (e: Even) : String :=
--   let aux s := if atTop then s else s!"({s})"
--   match e with
--   | Even.zero => "zero"
--   | Even.next n =>  aux s!"next {toString false n}"
-- instance : Add Even where
--   add := evenAdd
-- instance : Mul Even where
--   mul := evenMul
-- instance : ToString Even where
--   toString := toString true
-- #eval s!"Even 4 is {Even.next (Even.next Even.zero)}"
-- #eval s!"Even 0 is {Even.zero}"

def toString (atTop : Bool) (e: Even) : String :=
  let aux s := if atTop then s else s!"({s})"
  match e with
  | Even.zero => "zero"
  | Even.next n =>  aux s!"next {toString false n}"
instance : Add Even where
  add := evenAdd
instance : Mul Even where
  mul := evenMul
instance : ToString Even where
  toString := toString true

def even_four := Even.next (Even.next Even.zero)
def even_two := Even.next Even.zero
#eval s!"Even 4 is {even_four}"
#eval s!"Even 2 is {even_two}"

def even_16 := even_four + even_four + even_four + even_four
def even_32 := even_four * even_four * even_two
#eval s!"Even 16 is {even_16}"
#eval s!"Even 32 is {even_32}"

-- HttpMethod
inductive HttpMethod where
  | get
  | post
def HttpMethod.getName : HttpMethod → String
  | HttpMethod.get => "GET"
  | HttpMethod.post => "POST"

abbrev Uri := String
abbrev HttpVersion := Pos


structure HttpRequest where
  method : HttpMethod
  uri : Uri
  version : HttpVersion


-- HttpStatusCode
inductive HttpStatusCode where
  | ok
  | forbidden
  | notFound
  | unknown (code : Nat)

def statusFromNat (n: Nat) : HttpStatusCode :=
  match n with
    | 200 => HttpStatusCode.ok
    | 403 => HttpStatusCode.forbidden
    | 404 => HttpStatusCode.notFound
    | _ => HttpStatusCode.unknown n


instance : OfNat HttpStatusCode n where
  ofNat := statusFromNat n

def statusToString (status: HttpStatusCode) : String :=
  match status with
    | HttpStatusCode.ok => "200 OK"
    | HttpStatusCode.forbidden => "403 Forbidden"
    | HttpStatusCode.notFound => "404 Not Found"
    | HttpStatusCode.unknown n => s!"{n} Unknown"

instance : ToString HttpStatusCode where
  toString := statusToString


def test_http_status : HttpStatusCode := 200
#eval test_http_status



-- HttpResponse
structure HttpResponse where
  statusCode : Nat
  statusMessage : String

def resToString(res: HttpResponse) : String :=
  s!"[{res.statusCode}] {res.statusMessage}"
instance : ToString HttpResponse where
  toString := resToString

def uriList : List Uri := ["/", "/index", "/about", "/archive", "/contact"]
def getAvailableList' : List Uri → List Uri
  | uris =>
    let rec aux : List Uri → List Uri → List Uri
      | [], acc => acc
      | uri :: uris, acc =>
        if uri ≠ "/" then aux uris (uri :: acc) else aux uris acc
    aux uris []

def exceptUriFromList (uris : List Uri) (except : Uri): List Uri :=
  let rec aux : List Uri → List Uri → List Uri
    | [], acc => acc
    | uri :: uris, acc =>
      if uri = except then aux uris acc else aux uris (uri :: acc)
  aux uris []

def getUriList : List Uri := exceptUriFromList uriList "/"
def postUriList : List Uri := exceptUriFromList uriList "/"

def handleRequest (req : HttpRequest) : IO HttpResponse :=
  match req.method with
  | HttpMethod.get => do
    -- in get operation
    if req.uri ∈ getUriList then
      pure { statusCode := 200, statusMessage := "OK" }
    else
      pure { statusCode := 404, statusMessage := "Not Found" }

  | HttpMethod.post =>
    -- in post operation
    if req.uri ∈ postUriList then
      pure { statusCode := 200, statusMessage := "OK" }
    else
      pure { statusCode := 404, statusMessage := "Not Found" }

class HttpMethodHandler (α : Type) where
  handle : HttpRequest → IO HttpResponse

-- instance : HttpMethodHandler HttpRequest HttpResponse where
--   handler := handleRequest







-- instance : Handler HttpRequest HttpResponse where
--   handler := handleRequest
-- instance : ToString HttpRequest where
--   toString req := s!"[HTTP REQUEST] {req.method.getName} {req.uri} HTTP/{req.version}"
-- instance : ToString HttpResponse where
--   toString res := s!"[HTTP RESPONSE] {res.statusCode} {res.statusMessage}"

-- def main (args: List String) : IO UInt32 :=
--   match args with
--   | [] => pure 0
--   | args =>
--     match args.head! with
--     | "-h" | "--help" => do
--       IO.println "Usage: handle [METHOD][URL]"
--       IO.println "Method:\n\t-g\t--get:\tGET\n\t-p\t--post:\tPOST"
--       IO.println "-h\t--help\tDisplay this help message"
--       IO.println "URL:\n\t/\t/index\t/about\t/archive\t/contact"
--       pure 0
--     | "-g" | "--get" => do
