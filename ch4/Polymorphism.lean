-- Function that work on any overloading of kind of function
-- IO.println works on sort? of [ToString α] (any type that has an instance of ToString)
#check (IO.println)

def List.sum [Add α] [OfNat α 0] : List α → α
  | [] => 0 -- 0 is automatically coverted to type α through OfNat
  | x :: xs => x + xs.sum -- type α have instance of Add so that usage of '+'
#check List.sum
-- when check List.sum, [inst: Add α] named as instance implicits

def fourNats : List Nat := [1, 2, 3, 4]
#eval List.sum fourNats


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
#eval p1 + p2
