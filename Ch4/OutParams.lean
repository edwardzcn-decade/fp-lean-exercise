import Ch4.Polymorphism
import Ch4.PosTypeClasses


-- Example
-- def addNatPos : Nat → Pos → Pos
--   | 0, p => p
--   | n + 1, p => Pos.succ (addNatPos n p)

-- def addPosNat : Pos → Nat → Pos
--   | p, 0 => p
--   | p, n + 1 => Pos.succ (addPosNat p n)


-- Heterogeneous Overloading
#check @HAdd.hAdd
def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => addPosNat (p + 1) n --tail recursive?

def addPosNat' : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat' p n) -- not tail recursive? eq to (addPosNat' p n) + 1

def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => addNatPos n (p + 1)

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos



-- Reset toString
instance : ToString Pos where
  toString p:= s!"{p.toNat}"

-- #eval (12001: Pos) -- server stop (call rec function)
-- #eval (1200: Even) -- server stop (recursive instance search)

#check (3 : Pos) + (5 : Nat)
#eval (3 : Pos) + (5 : Nat)
#check (3 : Nat) + (5 : Pos)

class HPlus (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat
instance : HPlus Nat Pos Pos where
  hPlus := addNatPos
#check HPlus.hPlus (3 : Pos) (5 : Nat) -- we will see a metavariabele
-- #eval HPlus.hPlus (3 : Pos) (5 : Nat) --  typeclass instance problem
-- give specific output type
#eval (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos)

class HPlus' (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

-- The parameters that aren't needed to start instance search are outputs of the process, which is declared with the outParam modifier:
-- only search proper instance match `α` `β` type --- CONTROLLING INSTANCE SEARCH


-- Default Instances
-- start instance search with default types
-- instance [Add α] : HPlus' α α α where
--   hPlus a b:= Add.add a b

instance [HAdd α β γ] : HPlus' α β γ where
  hPlus := HAdd.hAdd

#eval s!"{ (4: Even) * (2: Even)}"
#eval s!"{HPlus'.hPlus (4 : Even) (2 : Even)}"  -- search instance `HAdd Pos Pos Pos`

#check HPlus'.hPlus (4 : Even) -- HPlus'.hPlus 4 : ?m.2483 → ?m.2485
-- can not search instance until all parameters are given

-- use default_instance
@[default_instance]
instance [Add α] : HPlus' α α α where
  hPlus := Add.add
#check HPlus'.hPlus (4 : Even) -- HPlus'.hPlus 4 : Even → Even

-- Default instances can also be assigned priorities that affect which will be chosen in situations where more than one might apply. For more information on default instance priorities, please consult the Lean manual.

-- Exercise

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p x := PPoint.ppoint (p.x * x) (p.y * x)

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
-- #eval 2* {x := 2.5, y := 3.7 : PPoint Float} -- error

instance [Mul α] : HMul α (PPoint α) (PPoint α) where
  hMul x p := PPoint.ppoint (x * p.x) (x * p.y)
#eval (2.0) * {x := 2.5, y := 3.7 : PPoint Float}

-- more general for any implemented instance `HMul β α α`
-- e.g.
-- #eval (2 : Nat) * (5 : Float)
def mulNatFloat : Nat → Float → Float
  | n, f => n.toFloat * f
instance : HMul Nat Float Float where
  hMul := mulNatFloat

instance [HMul β α α] : HMul β (PPoint α) (PPoint α) where
  hMul n p := PPoint.ppoint (n * p.x) (n * p.y)
#eval (2 : Nat) * {x := 2.5, y := 3.7 : PPoint Float}
