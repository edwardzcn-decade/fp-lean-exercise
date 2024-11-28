inductive Expr (op: Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op
  | unode : op → Expr op → Expr op
deriving Repr

inductive Arith where
  | plus
  | minus
  | times
  | div
deriving Repr

open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)

#eval twoPlusThree

def evaluateOption : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.unode p e1 =>
    evaluateOption e1 >>= fun v1 =>
    match p with
    | Arith.plus => pure v1
    | Arith.minus => pure (-v1)
    | Arith.times => none
    | Arith.div => if v1 == 0 then none else pure (1 / v1)
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    match p with
    | Arith.plus => pure (v1 + v2)
    | Arith.minus => pure (v1 - v2)
    | Arith.times => pure (v1 * v2)
    | Arith.div => if v2 == 0 then none else pure (v1 / v2)

def applyPrimOnBiOpOption : Arith → Int → Int → Option Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => if y == 0 then none else pure (x / y)

def applyPrimOnUnOpOption : Arith → Int → Option Int
  | Arith.plus, x => pure x
  | Arith.minus, x => pure (-x)
  | Arith.times, x => pure x
  | Arith.div, x =>
    if x == 0 then
      none
    else some (1 / x)

def evaluateOption' : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.unode p e1 =>
    evaluateOption' e1 >>= fun v1 =>
    applyPrimOnUnOpOption p v1
  | Expr.prim p e1 e2 =>
    evaluateOption' e1 >>= fun v1 =>
    evaluateOption' e2 >>= fun v2 =>
    applyPrimOnBiOpOption p v1 v2


def applyPrimOnBiOp : Arith → Int → Int → Except String Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrimOnUnOp : Arith → Int → Except String Int
  | Arith.plus, x => pure x
  | Arith.minus, x => pure (-x)
  | Arith.times, x => pure x
  | Arith.div, x =>
    if x == 0 then
      Except.error "Tried to divide x by zero"
    else pure (1 / x)


def evaluateExcept : Expr Arith → Except String Int
  | Expr.const i => pure i
  | Expr.unode p e1 =>
    evaluateExcept e1 >>= fun v1 =>
    applyPrimOnUnOp p v1
  | Expr.prim p e1 e2 =>
    evaluateExcept e1 >>= fun v1 =>
    evaluateExcept e2 >>= fun v2 =>
    applyPrimOnBiOp p v1 v2

-- open Expr in
-- open Arith in
-- def twoPlusThree : Expr Arith :=
--   prim plus (const 2) (const 3)


#eval evaluateExcept twoPlusThree


-- Try Monad
def evaluateMonad [Monad m] (applyPrimU: Arith → Int → m Int) (applyPrimO: Arith → Int → Int → m Int): Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.unode p e1 =>
    evaluateMonad applyPrimU applyPrimO e1 >>= fun v1 =>
    applyPrimU p v1
  | Expr.prim p e1 e2 =>
    evaluateMonad applyPrimU applyPrimO e1 >>= fun v1 =>
    evaluateMonad applyPrimU applyPrimO e2 >>= fun v2 =>
    applyPrimO p v1 v2

#eval evaluateMonad applyPrimOnUnOpOption applyPrimOnBiOpOption twoPlusThree -- some 5
#eval evaluateMonad applyPrimOnUnOp applyPrimOnBiOp twoPlusThree -- Except.ok 5

-- now continue to compose redundant code
-- define polymorphic applyPrimU

def applyDivOption (x : Int) (y : Int) : Option Int :=
    if y == 0 then
      none
    else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)


def applyPrimO [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => applyDiv x y

def applyPrimU [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → m Int
  | Arith.plus, x => pure x
  | Arith.minus, x => pure (-x)
  | Arith.times, x => pure x
  | Arith.div, x => applyDiv 1 x

-- rewrtie evaluateMonad as evaluateM

#eval evaluateMonad (applyPrimU applyDivOption) (applyPrimO applyDivOption) twoPlusThree
#eval evaluateMonad (applyPrimU applyDivExcept) (applyPrimO applyDivExcept) twoPlusThree
-- well... because of the name and polymorphic applyPrimU applyPrimO, now its longer...
--

-- type Prim depends on special , Prim(x)
inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

-- broaden the scope of oprations that may fail
inductive CanFail where
  | div

def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int): Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.unode _ _ => pure 0
  | Expr.prim p e1 e2 =>
    evaluateM applySpecial e1 >>= fun v1 =>
    evaluateM applySpecial e2 >>= fun v2 =>
    applyPrim applySpecial p v1 v2

-- Empty type and no effects

def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int := nomatch op

-- This can be used together with Id, the identity monad, to evaluate expressions that have no effects whatsoever:

-- just for passing type checking
def applyEmptyUp [Monad m] (op: Empty) (_ : Int) : m Int := nomatch op

open Expr Prim in

-- can not construct Empty type
-- #check evaluateM (m := Id) applyEmpty (prim (other CanFail.div) (const 5) (const 0))
-- application type mismatch
--   other CanFail.div
-- argument
--   CanFail.div
-- has type
--   CanFail : Type
-- but is expected to have type
--   Empty : Type

open Expr Prim in
#eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14)))


-- Nondeterministic Search
inductive Many (α : Type) where
| none : Many α
| more : α → (Unit → Many α) → Many α
-- different from List.cons: α → List α → List α to stores the rest of List (evaluation at once)
-- Many.more store a function that represents the rest of the computation (lazy evaluation)

-- A single result is represented by a `more` constructor that returns no further results:
def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)


def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)

def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)


-- Many is a monad
-- can prove

theorem noneLeftBind (f : α → Many β) : Many.bind (Many.none) f = Many.none := by rfl

theorem noneRightUnion : ∀ (m : Many α), Many.union m Many.none = m := by
  intro m
  induction m with
  | none => rfl
  | more a f ih =>
    -- one way
    -- unfold Many.union
    -- simp [ih]
    simp [Many.union]
    funext x
    exact ih x

theorem leftIdentityMany (x : α) (f : α → Many β) : Many.bind (Many.one x) f = f x := by
  unfold Many.one
  unfold Many.bind
  simp
  unfold Many.bind
  -- exact noneRightUnion (f x) -- or exact call noneRightUnion
  rw [noneRightUnion] -- rw the goal




theorem rightIdentityMany (m : Many α) : Many.bind m (Many.one) = m := by
  induction m with
  | none => rfl
  | more a f ih =>
    unfold Many.bind
    simp [ih]
    -- from here we can use rfl to automatically solve
    unfold Many.one
    unfold Many.union
    simp
    funext x
    unfold Many.union
    simp

theorem associativityMany (m : Many α) (f : α → Many β) (g : β → Many γ) : Many.bind (Many.bind m f) g = Many.bind m (fun x => Many.bind (f x) g) := by
  induction m with
  | none => rfl
  | more a h ih =>
    repeat rw [Many.bind]
    rw [←ih]
    sorry


    -- (Many.more a h).bind fun x => (f x).bind g

    -- ((f a).bind g).union ((h ()).bind fun x => (f x).bind g)
    -- unfold Many.bind
    -- simp
