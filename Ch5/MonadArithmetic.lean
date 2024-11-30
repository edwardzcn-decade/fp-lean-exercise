import Ch5.MonadClass
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


theorem unionAssoc (x y z : Many α) : (x.union y).union z = x.union (y.union z) := by
  induction x with
  | none => rfl
  | more a f ih =>
    repeat rw [Many.union] -- 3 times
    rw [ih]
    -- explanation


open Many in
theorem bindDistributeUnion (x y: Many α) (g: α → Many β) :
  bind (union x y) g = union (bind x g) (bind y g) := by
  induction x with
  | none => rfl
  | more a f ih =>
    rw [Many.bind]
    rw [Many.union]
    rw [Many.bind]
    rw [ih]
    -- now the goal
    -- (ga)∪(((f())≫=g)∪(y≫=g))=((ga)∪((f())≫=g))∪(y≫=g)
    -- apply unionAssoc
    rewrite [unionAssoc (g a) ((f ()).bind g) (y.bind g)]
    rfl

-- bindAssoc (monad required property)
theorem associativityMany (m : Many α) (f : α → Many β) (g : β → Many γ) : Many.bind (Many.bind m f) g = Many.bind m (fun x => Many.bind (f x) g) := by
  induction m with
  | none => rfl
  | more a h ih =>
    rewrite [Many.bind]
    rewrite [Many.bind]
    rewrite [←ih]
    let x := f a
    let y := (h ()).bind f
    -- rw
    have hx : x = f a := rfl
    have hy : y = (h ()).bind f := rfl
    rw [←hx, ←hy]
    -- sorry now we need bind distribute on union
    -- goal (x.union y).bind g = (x.bind g).union (y.bind g)
    rw [bindDistributeUnion x y g]

-- now we prove Many as a monad
instance : Monad Many where
  pure := Many.one
  bind := Many.bind


def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else
      Many.none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun answer =>
         pure (x :: answer))


instance [ToString α] : ToString (Many α) where
  toString m := toString (m.takeAll)

-- test
#eval s!"{addsTo 4 [1, 3, 5, 2, 1, 2]}"

inductive NeedsSearch
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y =>
    if y == 0 then
      Many.none
    else Many.one (x / y)
open Expr Prim NeedsSearch

#check Prim


def choose_plus_test := prim (other choose) (const (-5)) (const 5)

#eval (evaluateM applySearch (prim plus (const 1) (prim (other choose) (const 2) (const 5)))).takeAll
def choose_choose_test := (prim plus (prim (other choose) (const 1) (const 2)) (prim (other choose) (const 7) (const 8)))
#eval (evaluateM applySearch choose_choose_test).takeAll
#eval (evaluateM applySearch (prim (other div) (const 90) (prim plus (prim (other choose) (const (-5)) (const 5)) (const 5)))).takeAll
#eval evaluateM applySearch (prim plus (prim (other choose) (const (-5)) (const 5)) (const 5))
#eval evaluateM applySearch (prim (other choose) (const (-5)) (const 5))
-- bind in Monad Many unions all the results
#eval evaluateM applySearch (prim plus choose_plus_test choose_plus_test)
-- [10 ,0 ,0 10]

-- Custom Environments can be used as Monad
-- user-extensible and providing a mapping from strings to a function
-- give definition of Reader Monad in lean
-- pure/basic :: λe.e
-- for arithmic bops :: λe.f(e)+g(e)
-- for custrom ops :: λe.h(f(e) g(e))

def Reader (ρ : Type) (α : Type) := ρ → α
def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x
-- def Reader.bind : (Reader ρ α) → (α → Reader ρ β) → (Reader ρ β) := sorry

-- easier to understanding by expanding the definitions of `Reader`
-- def Reader.bind : ρ → α → (α → ρ → β) → (ρ → β) :=
-- sorry

-- def Reader.bind {ρ : Type} {α : Type} {β : Type}
--   (result : ρ → α) (next : α → ρ → β) : ρ → β :=
--   fun env => next (result env) env

def Reader.bind (result: Reader ρ α) (next: α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env
-- satisfy
instance : Monad (Reader rho) where
  pure := Reader.pure
  bind := Reader.bind
-- recall Id.bind
-- instance : Monad Id'' where
--   pure x := x
--   bind x f := f x
attribute [simp] Reader.bind Reader.pure
-- try proof Reader Monad property
def leftIdentityReader (x : α) (f : α → Reader ρ β) : bind (pure x) f = f x := by rfl
def rightIdentityReader (m : Reader ρ α) : Reader.bind m pure = m := by rfl
def associavityReader (m : Reader ρ α) (f : α → Reader ρ β) (g : β → Reader ρ γ) : bind (bind m f) g = bind m (fun x => bind (f x) g) := by rfl


--  pass Env as pair of (name, funciton to apply on two Ints e.g. max)
abbrev Env : Type := List (String × (Int → Int → Int))
def exampleEnv : Env := [("max", max), ("min", min), ("mod", fun x y => x % y)]

def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => Reader.pure 0
  | some f => Reader.pure (f x y)

#check applyPrimReader -- String → Int → Int → Reader Env Int
#check applySearch -- NeedsSearch → Int → Int → Many Int

-- compare to applySearch
-- FOR Many Monad using union and Many.bind
-- def applySearch : NeedsSearch → Int → Int → Many Int
--   | NeedsSearch.choose, x, y =>
--     Many.fromList [x, y]
--   | NeedsSearch.div, x, y =>
--     if y == 0 then
--       Many.none
--     else Many.one (x / y)
-- open Expr Prim NeedsSearch

-- call in evaluateM (above two are all applySpecial on special monad)
-- def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
--   | Prim.plus, x, y => pure (x + y)
--   | Prim.minus, x, y => pure (x - y)
--   | Prim.times, x, y => pure (x * y)
--   | Prim.other op, x, y => applySpecial op x y



open Expr Prim in
#eval evaluateM applyPrimReader (prim (other "max") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) exampleEnv


-- Exercise
-- 5.2.1
-- Check the monad contract for State σ and Except ε (Result ε in my implementation).
-- instance : Monad (Result ε) where
--   pure x := Result.ok x
--   bind res f := match res with
--     | Result.error e => Result.error e
--     | Result.ok x => f x
namespace MonadContractProof

theorem leftIdentityResult (x : α) (f : α → Result ε β) : bind (pure x) f = f x := by rfl
theorem rightIdentityResult (m : Result ε α) : bind m pure = m := by
  cases m with
  | error e => rfl
  | ok x => rfl
theorem associativityResult (m : Result ε α) (f : α → Result ε β) (g : β → Result ε γ) : bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  cases m with
  | error e => rfl
  | ok x => rfl
theorem leftIdentityState (x : α) (f : α → State α β) : bind (pure x) f = f x := by rfl
theorem rightIdentityState (m: State σ α) : bind m pure = m := by rfl
theorem associativityState (m : State σ α) (f : α → State σ β) (g : β → State σ γ) : bind (bind m f) g = bind m (fun x => bind (f x) g) := by rfl

end MonadContractProof


-- def Reader (ρ : Type) (α : Type) := ρ → α
-- Readers with Failure
def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α
-- Monad function with option return
def readOption : ReaderOption ρ ρ := fun env => some env
def ReaderOption.pure (x : α) : ReaderOption ρ α := fun _ => some x
def ReaderOption.bind (result : ReaderOption ρ α) (next : α → ReaderOption ρ β) : ReaderOption ρ β :=
  fun env => match result env with
    | none => none
    | some x => next x env
instance : Monad (ReaderOption ρ) where
  pure := ReaderOption.pure
  bind := ReaderOption.bind

theorem leftIdentityReaderOption (x : α) (f : α → ReaderOption ρ β) : bind (pure x) f = f x := by rfl
theorem rightIdentityReaderOption' (m : ReaderOption ρ α) : ReaderOption.bind m ReaderOption.pure = m := by
  funext env
  unfold ReaderOption.pure
  unfold ReaderOption.bind
  cases m env with
  | none => simp
  | some y => simp
theorem rightIdentityReaderOption (m : ReaderOption ρ α) : bind m pure = m := by
  -- `Monad.toBind.1` appears
  unfold bind
  funext env
  cases m env with
  | none => sorry
  | some x => sorry
theorem associavityReaderOption (m : ReaderOption ρ α) (f : α → ReaderOption ρ β) (g : β → ReaderOption ρ γ) : bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  funext env
  unfold bind
  cases m env with
  | none => sorry
  | some x => sorry

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α
-- Monad function with Except return
