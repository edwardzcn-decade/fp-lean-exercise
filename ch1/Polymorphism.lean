-- structure Point where
--   x : Float
--   y : Float
-- deriving Repr
-- #check (Point.mk : Float -> Float -> Point)


structure PPoint (α: Type) where
  ppoint::
  x : α
  y : α
deriving Repr

#check (PPoint Nat)

def natOrigin : PPoint Nat :=
{
  x := Nat.zero,
  y := Nat.zero
}

#eval natOrigin

def floatOrigin : PPoint Float :=
{
  x := 0.0,
  y := 0.0
}

#eval floatOrigin

def replaceX (a: Type) (origin: PPoint a) (newX: a) : PPoint a :=
{
  origin with
  x := newX
}

#eval replaceX Nat natOrigin 1
#eval natOrigin


inductive Signal where
| pos : Signal
| neg : Signal

def posOrNegThree (s: Signal)  : match s with | Signal.pos => Nat | Signal.neg => Int :=
match s with
| Signal.pos => (3: Nat)
| Signal.neg => (-3: Int)

#eval posOrNegThree Signal.pos

def length'' {α : Type} (xs : List α) : Nat :=
match xs with
| List.nil => Nat.zero
| List.cons _ xs' => Nat.succ (length'' xs')

#eval length'' (α := Nat) List.nil
#check length'' (α := Int)

inductive Option' (α : Type) : Type where
| none : Option' α
| some (value: α) : Option' α

def List.lengthInt := List.length (α := Int)
def l1: List Nat := [0,1,2,3,4]
def l2 := [-1,0,1]
#eval l2.lengthInt


def List.head?' {α : Type} (xs: List α) : Option α :=
match xs with
| [] => none
| h :: _ => some h

#print List.head!

def List.head!' {α : Type} [Inhabited α] (xs: List α) : α :=
match xs with
| [] => panic! "empty list"
| h:: _ => h

def getPairOfListsType {α : Type} : Type := (List α) × (List α)

abbrev PairStrings := getPairOfListsType (α := String)


def fives : PairStrings := (["five"], ["five"])
#eval fives

-- 和类型
inductive Sum' (α : Type) (β : Type) : Type where
  | inl : α → Sum' α β
  | inr : β → Sum' α β

inductive Sum'' (α : Type) (β : Type) : Type where
  | inl (a: α)
  | inr (b: β)



-- inductive MyType : Type where
  -- | ctor : (α : Type) → α → MyType
-- inductive MyType : Type where
--   | ctor (α : Type)

-- inductive MyType (α : Type) : Type where
--   | ctor : α → MyType α

-- def ofFive : MyType := ctor 5
-- Error type expected, got
  -- (MyType : Type → Type)


-- Exercise
-- Write a function to find the last entry in a list. It should return an Option.
def List.last?' {α : Type} (xs: List α) : Option α :=
match xs with
| [] => none -- empty list
| l :: [] => some l -- single element
| _ :: xs' => List.last?' xs' -- more than one


-- test
#eval List.last?' [1,2,3]
#eval List.last?' ["1"]

-- Write a function that finds the first entry in a list that satisfies a given predicate. Start the definition with def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=

def List.findFirst? {α : Type} (xs: List α) (predicate: α -> Bool) : Option α :=
match xs with
| [] => none
| l :: xs' => if predicate l then some l else List.findFirst? xs' predicate

#eval List.findFirst? [1,2,3] (fun x => x > 2)


-- Write a function Prod.swap that swaps the two fields in a pair. Start the definition with def Prod.swap {α β : Type} (pair : α × β) : β × α :=

def Prod.swap {α β : Type} (pair: α × β) : β × α :=
Prod.mk pair.snd pair.fst

-- Rewrite the PetName example to use a custom datatype and compare it to the version that uses Sum.

def PetName : Type := String ⊕ String

inductive PetName' : Type where
| dog(s: String) : PetName'
| cat(s: String) : PetName'

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets


def animals : List PetName := [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def animals' : List PetName' := [PetName'.dog "Spot", PetName'.cat "Tiger", PetName'.dog "Fifi", PetName'.dog "Rex", PetName'.cat "Floof"]

def howManyDogs' (pets: List PetName') : Nat :=
match pets with
| [] => 0
| PetName'.dog _ :: morePets => howManyDogs' morePets + 1
| PetName'.cat _ :: morePets => howManyDogs' morePets

-- what if add fish

def PetNameThree : Type := String ⊕ String ⊕ String

def animalsThree : List PetNameThree := [Sum.inl "Spot", Sum.inr (Sum.inl "Tiger"), Sum.inr (Sum.inr "Fish1"), Sum.inl "Fifi", Sum.inl "Rex", Sum.inr (Sum.inl "TT"), Sum.inr (Sum.inr "Fish2"), Sum.inr (Sum.inl "Floof")]


def howManyFish (pets: List PetNameThree) : Nat :=
match pets with
| [] => 0
| Sum.inl _ :: morePets => howManyFish morePets
| Sum.inr (Sum.inl _) :: morePets => howManyFish morePets
| Sum.inr (Sum.inr _) :: morePets => howManyFish morePets + 1

#eval howManyFish animalsThree

inductive PetNameThree' : Type where
| dog(s: String) : PetNameThree'
| cat(s: String) : PetNameThree'
| fish(s: String) : PetNameThree'

def howManyFish' (pets: List PetNameThree') : Nat :=
match pets with
| [] => 0
| PetNameThree'.dog _ :: morePets => howManyFish' morePets
| PetNameThree'.cat _ :: morePets => howManyFish' morePets
| PetNameThree'.fish _ :: morePets => howManyFish' morePets + 1

-- Write a function zip that combines two lists into a list of pairs. The resulting list should be as long as the shortest input list. Start the definition with def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=.

def zip {α β : Type} (xs: List α) (ys: List β) : List (α × β) :=
match xs, ys with
| [], _ => []
| _, [] => []
| x :: xs', y :: ys' => (x, y) :: zip xs' ys'

-- test
#eval zip [1,2,3] ["a", "b", "c","d"]


-- need fix
-- def cross {α β : Type} (xs: List α) (ys: List β) : List (α × β) :=
-- match xs, ys with
-- | [], _ => []
-- | x:: xs', [] => cross xs' ys -- need to be original whole y
-- | x:: xs', y:: ys' => (x,y) :: cross xs ys'




def cross {α β : Type} (xs: List α) (ys: List β) : List (α × β) :=
xs.bind (fun x => ys.map (fun y => {fst := x, snd := y}) )
-- test
#eval cross [1,2,3] ["a","b"]

def cross' {α β : Type} (xs: List α) (ys: List β) : List (α × β) :=
match xs,ys with
| [], _ => []
| x :: xs', ys =>
  let pairs_with_x := match ys with
  | [] => []
  | y :: ys' => (x, y) :: cross' [x] ys'
  pairs_with_x ++ cross' xs' ys

def cross'' {α β : Type} (xs: List α) (ys: List β) : List (α × β) :=
match xs,ys with
| [], _ => []
| x :: xs', ys =>
  let pairs_with_x := match ys with
  | [] => []
  | y :: ys' => (x, y) :: cross'' [x] ys'
  cross'' xs' ys ++ pairs_with_x

#eval cross' [1,2,3] ["a","b"]

#eval cross'' [1,2,3] ["a","b"]


-- Write a polymorphic function take that returns the first n
--  entries in a list, where n
--  is a Nat. If the list contains fewer than n entries, then the resulting list should be the input list. #eval take 3 ["bolete", "oyster"] should yield ["bolete", "oyster"], and #eval take 1 ["bolete", "oyster"] should yield ["bolete"].

def take {α : Type} (n: Nat) (xs: List α) : List α :=
match n with
| 0 => []
| Nat.succ n' => match xs with
  | [] => []
  | x :: xs' => x :: take (n') xs'

-- test
#eval take 2 ["bolete", "oyster"]

-- Using the analogy between types and arithmetic, write a function that distributes products over sums. In other words, it should have type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).
def prodOnSum {α β γ  : Type} (p: α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match p.snd with
  | Sum.inl b => Sum.inl (p.fst, b)
  | Sum.inr c => Sum.inr (p.fst, c)

-- test
#eval prodOnSum (3, @Sum.inl String Nat "dog")
#eval prodOnSum (3, @Sum.inr Nat Nat 4)

def multToSum {α : Type} (bool: Bool) (a: α) :=
  match bool with
  | true => Sum.inl a
  | false => Sum.inr a

def multToSum' : Bool -> α -> α ⊕ α
| true, a => Sum.inl a
| false, a => Sum.inr a

-- Conveniences
-- abbrev N := Nat
def length''' (xs: List α): Nat :=
  match xs with
  | [] => 0
  | _ :: xs' => length''' xs' + 1

#print List.length
#print length''
#print Option.getD

-- bug
-- def unzip pairs :=
--   match pairs with
--   | [] => ([], [])
--   | (x, y) :: xys =>
--     let unzipped := unzip xys
--     (x :: unzipped.fst, y :: unzipped.snd)


def iden (x: α) : α := x
def iden' (x: α) := x
def iden'' : α -> α := fun x => x

#check iden
#check iden'
#check iden''

-- ∀ (α : Type) (x : α), iden x = iden' x = iden'' x


def even' : Nat → Bool
| 0 => true
| Nat.succ n => !even' n

def double' : Nat → Nat := fun
| 0 => 0
| n + 1 =>  double' n + 2

def iden''' : α -> α := (.)


namespace FooMath
def triple : Nat -> Nat := (. * 3)
def quardruple : Nat -> Nat := (. * 4)
end FooMath

-- #check triple -- unkown namespace
#check FooMath.quardruple

open FooMath in
#check quardruple -- runnable

-- only in the last expr
-- #check quardruple -- unkown namespace

inductive Inline : Type where
| lineBreak
| string: String -> Inline
| emplh : Inline -> Inline
| strong : Inline -> Inline

def astrong : Inline := Inline.strong (Inline.string "strong")

def Inline.string? : Inline -> Option String := fun
| Inline.string s => some s
| _ => none

def Inline.string?' (inline: Inline) : Option String  :=
if let Inline.string s := inline then some s else none

open Inline in
#print string?

open Inline in
#print string?'
