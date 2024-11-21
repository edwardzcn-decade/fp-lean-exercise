-- Non-Empty Lists

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}



def NonEmptyList.get? {α : Type} : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n+1 => xs.tail.get? n
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by decide
theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by decide


-- gieve hte prop in bounds lead to no need for Option

def NonEmptyList.get {α : Type} (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n+1 => xs.tail[n]
-- how to trans to a proof version

--
class GetElem' (coll : Type) (idx : Type) (item : outParam Type) (inBounds : outParam (coll → idx → Prop)) where
  getElem' : (c : coll) → (i : idx) → inBounds c i → item
instance : GetElem' (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem' := NonEmptyList.get

-- class GetElem' (coll : Type) (idx : Type) (item : outParam Type) (inBounds : outParam (coll → idx → Prop)) where
--   getElem‘ : (c : coll) → (i : idx) → inBounds c i → item
-- instance : GetElem' (NonEmptyList α) Nat α (λ coll idx => coll.inBounds idx) where
--   getElem' := NonEmptyList.get
#check GetElem'.getElem'
#eval GetElem'.getElem' idahoSpiders 0 (by decide)
#eval GetElem'.getElem' idahoSpiders 1 (by decide)
-- #eval GetElem'.getElem idahoSpiders 5 (by decide) --fail for the bounder
