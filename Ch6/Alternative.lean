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
-- is equal to?
def checkCompanyAssoc (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
    (pure .company <*>
    checkName input.name)

-- class SeqRight' (f : Type → Type) where
--   seqRight : f α → (Unit → f β) → f β
----------------------------------  -------------- pure .company (β → γ)
-- target :  Validate (Field × String) Unit *> Validate (Field × String) (NonEmptyString → LegacyCheckedInput)
-- theorem eqSeqRightpure [Applicative ap] (f : α → β) (g : β → γ) : ap Unit *> pure g = pure (g ∘ f) :=
--   by
--     simp [Function.comp]
--     exact Applicative.seqRightIdentity ap g



-- one more simplification. For every `Applicative`, `pure F <*> E` is equivalent to `f <$> E`.

def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
    .company <$>
    checkName input.name
