-- Monad Class Type

#print Option
-- inductive Option.{u} : Type u → Type u
-- number of parameters: 1
-- constructors:
-- Option.none : {α : Type u} → Option α
-- Option.some : {α : Type u} → α → Option α


-- self-define Option' in Ch1
-- inductive Option' (α : Type) : Type where
-- | none : Option' α
-- | some (value: α) : Option' α

-- #print Option'
-- inductive Option' : Type → Type
-- number of parameters: 1
-- constructors:
-- Option'.none : {α : Type} → Option' α
-- Option'.some : {α : Type} → α → Option' α


-- And then (like in the Rust)
def andThen (option : Option α) (next : α → Option β) :=
  match option with
  | none => none
  | some value => next value

def getThirdFourth : List α → Option (α × α) :=
  fun list =>
  andThen list[2]? fun third =>
  andThen list[3]? fun fourth =>
  some (third, fourth)

-- here `list[2]` actually use List.get?

#eval getThirdFourth [5, 4, 3, 2, 1] -- some (3, 4)


-- assume use Except (defined inside Lean and in the textbook) as Result in Rust
inductive Result (ε : Type) (α : Type) where
| ok (x: α) : Result ε α
| error (e : ε) : Result ε α

#check List.get?

-- def get? : (as : List α) → (i : Nat) → Option α
--   | a::_,  0   => some a
--   | _::as, n+1 => get? as n
--   | _,     _   => none


def List.getResult {α : Type} (n: Nat) (l: List α) : Result String α :=
  -- Construct Result from option used `List.get?`
  match l[n]? with
  | none => Result.error s!"[Error] List.getResult error."
  | some a => Result.ok a


-- if not use List.get? ( a recursive function )
-- need to define inside List.getResult

def List.getResult' {α : Type} (n: Nat) (l: List α) : Result String α :=
  match l, n with
  | x::_, 0 => Result.ok x
  | _::xs, k + 1 => List.getResult' k xs
  | [] , _ => Result.error s!"[Error] List.getResult' error."


def getResultThirdFourth {α : Type} (l: List α) : Result String (α × α) :=
  match l[2]? with
  | none => Result.error s!"[Error] List.getResult error."
  | some a => match l[3]? with
    | none => Result.error s!"[Error] List.getResult error."
    | some b =>
    Result.ok (a, b)

-- define andThen for Result

def Result.andThen {α β ε: Type} (r: Result ε α) (f: α → Result ε β) : Result ε β :=
  match r with
  | ok x => f x
  | error e => Result.error e -- we need to construct Result ε β  from given instance e : ε  --care the type return is not ε

def rok  (x: α) : Result ε α := Result.ok x  -- with the help of automatic implicit arguments we dont need to give {α ε :Type}
def rfa  (e: ε) : Result ε α := Result.error e

-- rewrite some func

def List.getResult'' (n: Nat) (l : List α) : Result String α :=
  match l[n]? with
  | none => rfa s!"[Error] List.getResult'' error."
  | some x => rok x

-- use Result.andThen
def getResultThirdFourth' (l: List α) : Result String (α × α) :=
  Result.andThen (List.getResult'' 2 l) fun third =>
  Result.andThen (List.getResult'' 3 l) fun fourth =>
  rok (third,fourth)

-- try use accessor dot notation
def getResultThirdFourth'' (l: List α) : Result String (α × α) :=
  (List.getResult'' 2 l).andThen fun third =>
  (List.getResult'' 3 l).andThen fun fourth =>
  rok (third, fourth)

-- use infix operators
infixl:55 " ~~> " => Result.andThen
infixl:90 " <r> " => List.getResult
def getResultThirdFourth''' (l: List α) : Result String (α × α) :=
  2 <r> l ~~> fun third =>
  3 <r> l ~~> fun fourth =>
  rok (third, fourth)

-- try a proof
theorem eqGetResultThirdFourth  : getResultThirdFourth [1,2,3,4]  = getResultThirdFourth''' [1,2,3,4] := by
  unfold getResultThirdFourth getResultThirdFourth'''
  unfold Result.andThen
  unfold List.getResult
  simp
  unfold rok
  rfl
--

-- For larger
def noobGetResultEvenPositions (l: List α) : Result String (α × α × α × α) :=
  0 <r> l ~~> fun u0 =>
  2 <r> l ~~> fun u1 =>
  4 <r> l ~~> fun u2 =>
  6 <r> l ~~> fun u3 =>
  rok (u0,u1,u2,u3)
