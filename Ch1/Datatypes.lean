-- Sum Type
-- Recursive Datatype (including itself)
-- Recursive sum types are called inductive datatypes


-- inductive Bool where
--   | true : Bool
--   | false : Bool


-- inductive Nat': Type where
--   | zero : Nat'
--   | succ (n: Nat') : Nat'


-- def odd (n: Nat) : Bool :=
-- match n with
-- | Nat.zero => Bool.false
-- | Nat.succ k => not (even k)

-- def even (n: Nat) : Bool :=
-- match n with
-- | Nat.zero => Bool.true
-- | Nat.succ k => not (odd k)

def pred (n: Nat): Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

def plus (n k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')

def times (n k: Nat): Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n k: Nat): Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')
-- div prove termination
