import Ch4.Indexing
import Ch4.StandardClasses

#check List.map
-- (α → β) → List α → List β
#check @Functor.map
-- f turns Type u_1 to another leval Type u_2 (like Int to List Int)
-- (α → β) → f α → f β where α and β are in type layer u_1

-- Monad.bind ==> Applicative.?seq ==> Functor.map ?


-- `seq` is much like map
-- f (α → β) → (Unit → f α) → f β
-- Applicative Functor
instance : Applicative Option where
  pure x := .some x  -- .some call Option.some?
  seq f x :=
    match f with
    | none => none
    | some f' => f' <$> x ()

instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .error e => .error e
    | .ok f' => f' <$> x ()

-- e.g. some Plus.plus <*> some 4 <*> some 5

-- Not every functor is applicative. Pair is like the built-in product type Prod:
structure Pair (α β : Type) : Type where
  first : α
  second : β

instance : Functor (Pair α) where
  map f x := ⟨ x.first, f x.second ⟩
-- only affects the second element

-- check Functor Contract
-- id <$> Pair.mk x y = Pair.mk x y
theorem leftIdPair : id <$> Pair.mk x y = Pair.mk x y := by rfl
theorem composeFunPair : f <$> g <$> Pair.mk x y = (f ∘ g) <$> Pair.mk x y := by rfl

-- cannot define a instance of Applicative
-- def Pair.pure (x : β) : Pair α β := Pair.mk _ x -- cannot define this
-- cannot define a instance of Monad either

-- `Validate` an example of Applicative Functor

structure RawInput where
  name : String
  birthYear : String


-- Fast pos according to subtype defination
def FastPos : Type := {x : Nat // x > 0}

#print FastPos

-- def one with  Nat instance and proof object
-- the ⟨ ⟩ shows the structure type like contructor
def one : FastPos := ⟨1, by simp⟩

instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp_arith⟩

-- The `simp_arith` tactic is a version of simp that takes additional arithmetic identities into account.

-- using proof object with a name
def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else none

-- now construct using subType
structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
deriving Repr

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
deriving Repr

instance : Functor (Validate ε) where
  map f
   | .ok x => .ok (f x)
   | .errors errs => .errors errs -- cumulative errors as func?

def Field := String

instance : HAppend (NonEmptyList α) (NonEmptyList α) (NonEmptyList α) := {
  hAppend := fun x y => { head := x.head, tail := x.tail ++ y.toList }
}

instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')


def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }


-- {n : String // n ≠ ""} describes subtype of String which is not empty, used to construct Validate
-- the return Validate ε α
-- polymorphic ε turns to Field × String as error message
-- polymorphic α turns to String subtype (String with property that it is not empty) using `{}` notion


-- use if else branch to construct Validate
def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required" -- just like return Result.error e
  else pure ⟨name, h⟩ -- just like return Result.ok x (pure method of Result). Here we need add with proof object (n ≠ "")

--  Monad bind?
def Validate.andThen (val : Validate ε α) (next : α → Validate ε β)  : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x

-- use match to construct Validate
def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none =>
    reportError "birth year" "Must be a natural number"
  | some y => pure y

def checkBirthYear (thisYear year: Nat) : Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  -- if h: year > 1900 ∧ year ≤ thisYear then
  --   pure ⟨year, by simp [*]⟩
  -- else reportError "year" "Out of range"
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, ⟨h, h'⟩⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"

-- combine the three components
def checkInput (year : Nat) (rawinput: RawInput) : Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName rawinput.name <*>
    (checkYearIsNat rawinput.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear year birthYearAsNat

#eval checkInput 2023 {name := "David", birthYear := "1984"}
#eval checkInput 2023 {name := "", birthYear := "2045"}
#eval checkInput 2023 {name := "David", birthYear := "syzygy"}
