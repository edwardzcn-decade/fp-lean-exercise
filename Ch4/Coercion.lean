import Ch4.StandardClasses

#eval [1,2,3,4].drop (2: Nat)
-- def t := [1,2,3,4].drop (2: Pos) -- fail
def corecion_t1 : List Nat := [1,2,3,4].drop (2: Pos).toNat
-- def corecion_t2 : List Nat := [1,2,3,4].drop (2: Pos) -- fail
-- def corecion_t3 := ((3 : Pos) : Nat) --fail

-- need coercions
#check Coe.coe
instance : Coe Pos Nat where
  coe := Pos.toNat

-- try again
def corecion_t2 : List Nat := [1,2,3,4].drop (2: Pos)
def corecion_t3 := ((3 : Pos) : Nat)

#check @corecion_t3
#check [1,2,3,4].drop (2: Pos)

#print NonEmptyList.toList

def NonEmptyList.toList' {α : Type} (nl : NonEmptyList α) : List α :=
  nl.head :: nl.tail
#print NonEmptyList.toList'

theorem eqNonEmptyListToList {α : Type} (nl : NonEmptyList α) : nl.toList = nl.toList' := by
  unfold NonEmptyList.toList
  unfold NonEmptyList.toList'
  simp -- solve by simp directly

-- now we have NonEmptyList.toList
-- to achieve coercion

instance : Coe (NonEmptyList α) (List α) where
  coe := NonEmptyList.toList
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := {head := x, tail := xs}

#check ([1,2,3,4,5,] : NonEmptyList Nat)



structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }


-- My version
def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec aux (acc: M.Carrier) (l: List α) : M.Carrier :=
    match l with
    | [] => acc
    | y :: ys => aux (Monoid.op M acc (f y)) ys
  aux M.neutral xs

def foldMap' (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs


-- try proof?
theorem eqFoldMapOnMonoid  (M : Monoid) (f: α → M.Carrier) (xs : List α) :   foldMap M f xs = foldMap' M f xs := by
  unfold foldMap
  unfold foldMap'
  induction xs with
    | nil =>
      -- Base case, both are immediately the neutral element
      unfold foldMap.aux
      unfold foldMap'.go
      rfl
    | cons x xs ih =>
      -- Inductive step
      unfold foldMap.aux
      unfold foldMap'.go
      sorry --fail

instance : CoeSort Monoid Type where
  coe := Monoid.Carrier
def foldMap'' (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys -- actually call go (M.op soFar ((f y) : M.Carrier)) ys
  go M.neutral xs

-- instance boolToProp : Coe Bool Prop where
--   coe b := Eq b true

instance : CoeSort Bool Prop where
  coe b := b = true

-- use bool evidence (beq) as eq

-- coercing to functions
-- https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html#coercing-to-functions
-- corecion to functions (json incode / decode according to contents)
example : NonEmptyList String :=
  { head := "Sparrow",
    tail := ["Duck", "Swan", "Magpie", "Eurasian coot", "Crow"]
  }

example (n : Nat) (k : Nat) : Bool :=
  n + k == k + n

-- use example (nameless instance of type or function)
