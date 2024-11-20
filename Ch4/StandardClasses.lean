import Ch4.Polymorphism
import Ch4.PosTypeClasses
#check 2<4
-- def test_boolean_equality := if 2 < 4 then 4 else 2 --ok
-- def test_propositional_equality := if ((fun x : Nat => x + 1) = (Nat.succ ·)) then "yes" else "no" -- failed to synthesize Decidable ((fun x => x + 1) = fun x => x.succ)

-- Propositional equality is the mathematical statement that two things are equal.
-- write with single equals sign `=`

-- Boolean equality is the same kind of equality that is found in other pl.
-- comparing the value using `==`
-- `==` is overloaded using a type class. `x == y` is shorhand for `BEq.beq x y`

-- overload order/compare using ≤ ≥ < > like + *,
#check Ordering
-- inductive Ordering where
--   | lt | eq | gt
-- deriving Inhabited, BEq
#check Ord
-- class Ord (α : Type u) where
--   /-- Compare two elements in `α` using the comparator contained in an `[Ord α]` instance. -/
--   compare : α → α → Ordering

#check ((fun x : Nat => x + 1) = (Nat.succ ·))
def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ m, Pos.succ n => comp m n

instance : Ord Pos where
  -- as description in Ord type class
  -- compare := Pos.comp compare : α → α → Ording
  compare := Pos.comp


-- Hash
#check Hashable
-- /-- Hashes the value `a : α` into a `UInt64`. -/
--   hash : α → UInt64
#check mixHash
  -- UInt64 → UInt64 → UInt64

-- BinTree
-- if designed in c++
-- template <typename T>
-- class BinTreeNode {
-- public:
--     T value;
--     BinTreeNode<T>* left;
--     BinTreeNode<T>* right;

--     BinTreeNode(T value) : value(value), left(nullptr), right(nullptr) {}
-- };

-- α is not used actually
-- dont have polymorphism noun
inductive Noden where
  | noden
  deriving Repr

inductive Node (α : Type) where
  | node (a: α)
  deriving Repr

inductive OnlyRootTree (α : Type) where
  | root: Node α → OnlyRootTree α
  deriving Repr

-- One leaf tree
inductive OneLeafTree (α : Type) where
  | oneleaf: Node α → Node α → OneLeafTree α
  deriving Repr

-- or you can give
inductive OneLeafOrRootTree (α: Type) where
  | root (r: Node α)
  | oneleaf (l: Node α) (r: Node α)
  deriving Repr

-- eq to
inductive OneLeafOrRootTree' (α: Type) where
  | root : Node α → OneLeafOrRootTree' α
  | oneleaf : Node α → Node α → OneLeafOrRootTree' α
  deriving Repr

def test_one_leaf : OneLeafOrRootTree' Nat := OneLeafOrRootTree'.root (Node.node 3)
#eval test_one_leaf

-- according to the text book BinTree
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | node (l : BinTree α) (v: α) (r : BinTree α)
  deriving Repr

abbrev BinTree.notEmpty {α : Type} (b: BinTree α): Prop :=
  b ≠ BinTree.leaf


def BinTree.selectTop {α : Type} (b: BinTree α) (ok : b.notEmpty) : α := by
  unfold BinTree.notEmpty at ok
  match b with
  | BinTree.leaf => contradiction
  | BinTree.node _ v _ => exact v


-- eq to
def BinTree.selectTop' {α : Type} (b: BinTree α) (ok : b.notEmpty) : α :=
  match b with
  | BinTree.leaf => by contradiction
  | BinTree.node _ v _ => v

theorem binSelectTopEq {α : Type}: ∀ (b : BinTree α), BinTree.selectTop b = BinTree.selectTop' b := by
  intro h
  match h with
  | BinTree.leaf =>
    unfold BinTree.selectTop
    simp
    unfold BinTree.selectTop'
    simp
  | BinTree.node l v r =>
    unfold BinTree.selectTop
    simp
    unfold BinTree.selectTop'
    simp



-- Example usage
def exampleTree : BinTree Nat :=
  BinTree.node (BinTree.node BinTree.leaf 1 BinTree.leaf) 2 (BinTree.node BinTree.leaf 3 BinTree.leaf)
theorem exampleTreeBound: exampleTree.notEmpty := by
  unfold exampleTree
  simp

#eval BinTree.selectTop exampleTree exampleTreeBound -- 2


def exampleLeaf : BinTree Nat :=
  BinTree.leaf
theorem exampleLeafBound: exampleLeaf.notEmpty := by
  unfold exampleLeaf
  simp
  sorry
  -- False can not prove!
-- #eval BinTree.selectTop exampleLeaf --wrong  -- can not give bound/evidence because we canot prove



def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf => true
  | BinTree.node _ _ _, BinTree.leaf => false
  | BinTree.leaf, BinTree.node _ _ _ => false
  | BinTree.node l1 v1 r1, BinTree.node l2 v2 r2 => v1 == v2 && eqBinTree l1 l2 && eqBinTree r1 r2

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf => 0 -- no value to hash
  | BinTree.node l v r => mixHash 1 (mixHash (hash v) (mixHash (hashBinTree l) (hashBinTree r)))
-- leave hash v after children

def hashBinTree' [Hashable α] : BinTree α → UInt64
  | BinTree.leaf => 0
  | BinTree.node l v r =>
    mixHash 1 (mixHash (hashBinTree l) (mixHash (hash v) (hashBinTree r)))
-- leave hash v in the middle

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

#check List.append
#check @Append.append
#check @HAppend.hAppend

-- TODO 4.5 exercise
