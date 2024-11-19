-- Function that work on any overloading of kind of function
-- IO.println works on sort? of [ToString α] (any type that has an instance of ToString)
#check (IO.println)
#check @IO.println
#check List.foldl
#check @List.foldl

def List.sum [Add α] [OfNat α 0] : List α → α
  | [] => 0 -- 0 is automatically coverted to type α through OfNat
  | x :: xs => x + xs.sum -- type α have instance of Add so that usage of '+'
#check List.sum
-- when check List.sum, [inst: Add α] named as instance implicits

def fourNats : List Nat := [1, 2, 3, 4]
#eval List.sum fourNats

def List.together [Append α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x ++ xs.together

instance : OfNat String 0 where
  ofNat := ""
#eval List.together ["a", "b", "c", "d"]

structure PPoint (α : Type) where
ppoint::
  x : α
  y : α
deriving Repr

def p1 := PPoint.ppoint 1 2
def p2 := PPoint.ppoint 0 2
#eval p1


-- without instance implicits
-- instance : Add Pos where
--   add := Pos.plus


def addPPoint [Add α] : PPoint α → PPoint α → PPoint α
  | PPoint.ppoint x1 y1, PPoint.ppoint x2 y2 => PPoint.ppoint (x1 + x2) (y1 + y2)
instance [Add α] : Add (PPoint α) where
  add := addPPoint

-- or we can write (explicitly giving instance semantics)
instance [Add α] : Add (PPoint α) where
  add p1 p2 := addPPoint p1 p2
instance [Add α] : Add (PPoint α) where
  add p1 p2 := PPoint.ppoint (p1.x + p2.x) (p2.x + p2.y)
#eval p1 + p2

#check Fin.add -- check a structure's accessors

-- In order for Lean to find an instance, its arguments must be available. This means that each argument to the type class must be an argument to the method that occurs before the instance
#check @Add.add -- {α : Type} is implicit and appears before the instance
#check @OfNat.ofNat -- {α : Type} is implicit and appears before the instance, but (n: Nat) is a little bit tricky for a more convinent way to use


-- Exercise
-- 0. Even Numbers Define a datatype that represents only even numbers. Define instances of Add, Mul, and ToString that allow it to be used conveniently. OfNat requires a feature that is introduced in the next section.
-- 1. Write an instance of OfNat for the even number datatype from the previous section's exercises that uses recursive instance search. For the base instance, it is necessary to write OfNat Even Nat.zero instead of OfNat Even 0.

inductive Even
  | zero: Even
  | succ(n: Even): Even



def evenToString (atTop: Bool) (e: Even) : String :=
  let aux s:= if atTop then s else s!"({s})"
  match e with
    | Even.zero => "Even.zero"
    | Even.succ n => aux s!"Even.succ {evenToString false n}"
#print evenToString

instance : ToString Even where
  toString e := evenToString true e

def even0 := Even.zero
def even2 := Even.succ Even.zero
def even4 := Even.succ (Even.succ Even.zero)

#eval println!"There are\n0\t{even0}\n2\t{even2}\n4\t{even4}"

def addEven: Even → Even → Even
  | Even.zero, e => e
  | Even.succ n, e => Even.succ (addEven n e)
instance : Add Even where
  add := addEven

def mulEven: Even → Even → Even
  | Even.zero, _ => Even.zero
  | Even.succ n, e => addEven e (addEven e (mulEven n e))
instance : Mul Even where
  mul := mulEven

#eval println!"There are\n8\t{even2 * even4}\n10\t{even2 * even4 + even2}"


-- not a good answer
-- another way? just like use `let rec` in instance OfNat Pos (n + 1)
--
-- instance : OfNat Even n where
--   ofNat :=
--     let rec aux (n: Nat) : Even := match n with
--       | 0 => Even.zero
--       | 1 => panic! "Impossible"
--       | n + 2 => Even.succ (aux n)
--     aux n

instance : OfNat Even Nat.zero where
  ofNat := Even.zero

instance (n : Nat) [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := Even.succ (OfNat.ofNat n)


def test_even_0: Even := 0
def test_even_2: Even := 2
#eval test_even_2
-- def test_even_1: Even := 1 -- absence of the instance above (correct)
def test_even_254: Even := 254
-- def test_even_256: Even := 256 --absence of the instance above (due to recursive search limit)
-- OK
-- #eval test_even_254 -- ok
