inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def three' : Pos := Pos.succ (Pos.succ Pos.one)
-- Add Mul not support
-- def Pos.six : three' + three'

class Plus (α : Type) where
  plus : α → α → α

class PlusChange (α : Type) (β : Type) where
  plus_change : α → β → β

#check Plus
#check Nat.add


def Nat.plus' := Nat.add
#check Nat.plus'
instance : Plus Nat where
  plus := Nat.plus'

-- named in Plus.plus
#check Plus.plus

#eval Plus.plus 3 5
open Plus (plus)
#eval plus 3 5


def Pos.plus : Pos → Pos → Pos :=
  fun x y => match x with
    | Pos.one => Pos.succ y
    | Pos.succ x' => Pos.succ (Pos.plus x' y)

def Pos.plus' : Pos → Pos → Pos
  | Pos.one, y => y
  | Pos.succ x', y => Pos.succ (Pos.plus' x' y)

instance : Plus Pos where
  plus := Pos.plus

def six' : Pos := plus three' three'


def Pos.plus_to_Float : Pos → Float → Float
  | Pos.one, y => (Nat.toFloat 1) + y
  | Pos.succ x', y => Pos.plus_to_Float x' y + 1.0
instance : PlusChange Pos Float where
  plus_change := Pos.plus_to_Float
def six_change' := PlusChange.plus_change three' 3.0
#eval six_change'
#check six_change'

-- hAdd heterogeneous addition
instance : Add Pos where
  add := Pos.plus


def six'' : Pos := three' + three'
theorem six''_eq_six' : six'' = six' := by
  rw [six'']
  rw [six']
  show Pos.plus three' three' = Pos.plus three' three'
  apply Eq.refl
-- Finish

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"


def aux : Bool → String → String :=
  fun b s => if b then s else "(" ++ s ++ ")"
def aux' (atTop :Bool) (p : Pos) : String :=
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ p' => aux atTop s!"Pos.succ {aux' false p'}"
def posToString' (_ : Bool) (p : Pos) : String :=
  aux' false p

instance : ToString Pos where
  toString := posToString' true

#eval s!"There are {Pos.one}"
#eval s!"There are {Pos.succ Pos.one}"
#eval s!"There are {six''}"



def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => Pos.toNat n + 1

instance : ToString Pos where
  toString x := toString (x.toNat)
#eval s!"There are {six''}"

def Pos.toFloat : Pos → Float
  | Pos.one => 1.0
  | Pos.succ n => Pos.toFloat n + 1.0
instance : ToString Pos where
  toString x := toString (x.toFloat)
-- left part: toString x, give an instance for toString: Pos → String apply on x: Pos
-- right part: toString (x.toFloat), calculate toString: Float → String applyed on x.toFloat: Float (expand toFloat x, calling Pos → Float applyed on x: Pos)
-- left type: Pos → String [ Pos ] => String
-- right type: Float → String [ Pos → Float [ Float ] ] => Float → String [ Float ] => String
#eval s!"There are {six''}"

def Pos.mul : Pos → Pos → Pos
  | Pos.one, y => y
  | Pos.succ x', y => Pos.plus y (Pos.mul x' y)

def Pos.mul' : Pos → Pos → Pos
  | Pos.one, y => y
  | Pos.succ x', y => y + Pos.mul' x' y

#check Mul
instance: Mul Pos where
  mul := Pos.mul

def four' : Pos := Pos.succ three'
def twelve' : Pos := three' * four'
#eval s!"3.0 * 4.0 = {twelve'}" -- due to toString transfer Float first

-- Literal Numbers
#check OfNat
#check Mul
#check Add


inductive LT4 where
| zero
| one
| two
| three
deriving Repr

instance : OfNat LT4 0 where
  ofNat := LT4.zero

def lT4ToString : LT4 → String
  | LT4.zero => "[LT4]zero"
  | LT4.one => "[LT4]one"
  | LT4.two => "[LT4]two"
  | LT4.three => "[LT4]three"

instance : ToString LT4 where
  toString := lT4ToString
#eval s!"{LT4.two}"

def lT4ToNat : LT4 → Nat
  | LT4.zero => 0
  | LT4.one => 1
  | LT4.two => 2
  | LT4.three => 3
instance : ToString LT4 where
  toString := toString ∘ lT4ToNat
  -- (f ∘ g) of which
    -- f : Nat → String
    -- lT4ToNat : LT4 → Nat
    -- "instance : ToString Nat" have already defined in Nat

#eval s!"{LT4.zero}"


instance : OfNat LT4 0 where
  ofNat := LT4.zero
instance : OfNat LT4 1 where
  ofNat := LT4.one
instance : OfNat LT4 2 where
  ofNat := LT4.two
instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4)
#eval s!"evaluation 3 of LT4 '{(3 : LT4)}'"


instance : OfNat Pos (n + 1) where --- care for match pattern (n + 1)
-- contruct Pos from n : Nat and build actually greater 1
-- but assume n + 1
-- so that is eq
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | n + 1 => Pos.succ (natPlusOne n)
    natPlusOne n

def eight'' : Pos := 8
#eval eight''


-- exercise in TypeClassesExercise.lean
#print Pos
