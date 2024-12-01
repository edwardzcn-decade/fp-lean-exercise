structure MythicalCreature where
  large : Bool
deriving Repr

#check MythicalCreature
#check MythicalCreature.mk
#check MythicalCreature.large

structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr

#check Monster
#check Monster.mk
#check Monster.toMythicalCreature

def troll : Monster where
  large := true
  vulnerability := "fire"

#check troll
#check troll.toMythicalCreature -- erase the underlying information and move up the inheritance hierarchy


def troll2 : Monster := {
  large := true
  vulnerability := "sunlight"
}
-- def troll3 : Monster := ⟨true, "night"⟩
-- error message (need to call MythicalCreature.mk implicitly using another layer of ⟨ ⟩ )
-- application type mismatch
--   Monster.mk true
-- argument
--   true
-- has type
--   Bool : Type
-- but is expected to have type
--   MythicalCreature : Type

structure SpecialMonster where
  large : Bool
  weak : String
deriving Repr
def specialTroll : SpecialMonster := ⟨true, "night"⟩ -- no need for another layer
def troll4 : Monster := ⟨⟨true⟩, "test"⟩

-- Multiple inheritance
structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr

def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"


structure MonstrousAssistant extends Monster, Helper where
deriving Repr

def domesticatedTroll : MonstrousAssistant where
  large := true
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"

-- diamond problem
--   A
--  / \
-- B   C
--  \ /
--   D
-- e.g. A type is MythicalCreature, B and C are Monster and Helper, D is MonstrousAssistant

-- Lean
-- In Lean, the answer is that the first specified path to the grandparent structure is taken, and the additional parent structures' fields are copied rather than having the new structure include both parents directly.

#check MonstrousAssistant.mk
-- MonstrousAssistant.mk (toMonster : Monster) (assistance payment : String) : MonstrousAssistant


#print MonstrousAssistant.toMonster -- grab from the constructor
-- @[reducible] def MonstrousAssistant.toMonster : MonstrousAssistant → Monster :=
-- fun self => self.1
#print MonstrousAssistant.toHelper -- construct from the fields
-- @[reducible] def MonstrousAssistant.toHelper : MonstrousAssistant → Helper :=
-- fun self => { toMythicalCreature := self.toMythicalCreature, assistance := self.assistance, payment := self.payment }


-- Default Declarations
inductive Size where
  | small | medium | large | huge
deriving BEq -- for ==

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large ∨ size == Size.huge

#print SizedCreature

abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)

def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by decide

#eval huldre.large
