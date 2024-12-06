import Ch6.ApplicativeContract
abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) →
    NonEmptyString →
    LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr

-- A validator for these rules is more complicated.
-- It's easier to design the three cases independently and then combine them.


---
def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 =>  .errors (errs1 ++ errs2)
---
-- This pattern of recovery from failure is common enough that Lean has built-in syntax for it,
class OrElse' (α : Type) where
  orElse : α → (Unit → α) → α -- Validate ε α → (Unit → Validate ε α) → Validate ε α

-- This pattern of omit the first return of `<*>` (not using f α)
class SeqRight' (f : Type → Type) where
  seqRight : f α → (Unit → f β) → f β


instance : OrElse (Validate ε α) where
  orElse := Validate.orElse
-- `E1 <|> E2` is short for `OrElse.orElse E1 (fun () => E2)`


def checkThat (condition : Bool) (field : Field) (msg : String) : Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg

-- Use Applicative Contract 4th
-- u <*> pure x = pure (fun f => f x) <*> u
-- The ordering of pure operations doesn't matter
-- to reorder (refactor the checkCompany)
-- from
def checkCompany'' (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  pure (fun () name => .company name) <*>
    checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" <*>
    checkName input.name
-- to
def checkCompany' (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
    pure .company <*>
    checkName input.name


-- f <*> pure x = pure (f x)
-- also ?
-- f *> pure x = pure (f x) well .. cannot prove the control flow now
-- neither does the simplification

-- one more simplification. For every `Applicative`, `pure F <*> E` is equivalent to `f <$> E`.

def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
    .company <$>
    checkName input.name

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }

def checkHumanBefore1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970) ("birth year", "less than 1970") <*>
      pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970) ("birth year", "greater than 1970") <*>
      checkName input.name

def checkLegacyInput (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input

#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkLegacyInput ⟨"Johnny", "1963"⟩
#eval checkLegacyInput ⟨"", "1963"⟩

#check Type 1

-- inductive MyList (α : Type 1) : Type where
--   | nil : MyList α
--   | cons : α → MyList α → MyList α
-- error meesage : invalid universe level in constructor
-- solve by define in Type 1 universe level
inductive MyList' (α : Type 1) : Type 1 where
  | nil : MyList' α
  | cons : α → MyList' α → MyList' α


-- in any universe level
inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons : α → MyList α → MyList α
deriving Repr

def myListOfNumbers : MyList Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNumberType : MyList Type :=
  .cons Nat (.cons Int .nil)

#eval myListOfNumbers -- could print
-- #eval myListOfNumberType· -- cound not print
-- has type
--   MyList Type
-- but instance
--   Lean.Eval (MyList Type)

inductive Sum''' (α : Type u) (β : Type u) : Type u where
  | inl : α → Sum''' α β
  | inr : β → Sum''' α β
