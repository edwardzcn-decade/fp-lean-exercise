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
def evalueteMonad [Monad m] (applyPrimU: Arith → Int → m Int) (applyPrimO: Arith → Int → Int → m Int): Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.unode p e1 =>
    evalueteMonad applyPrimU applyPrimO e1 >>= fun v1 =>
    applyPrimU p v1
  | Expr.prim p e1 e2 =>
    evalueteMonad applyPrimU applyPrimO e1 >>= fun v1 =>
    evalueteMonad applyPrimU applyPrimO e2 >>= fun v2 =>
    applyPrimO p v1 v2

#eval evalueteMonad applyPrimOnUnOpOption applyPrimOnBiOpOption twoPlusThree -- some 5
#eval evalueteMonad applyPrimOnUnOp applyPrimOnBiOp twoPlusThree -- Except.ok 5

-- now continue to compose redundant code
-- define polymorphic applyPrimeU

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

def applyPrimeU [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → m Int
  | Arith.plus, x => pure x
  | Arith.minus, x => pure (-x)
  | Arith.times, x => pure x
  | Arith.div, x => applyDiv 1 x

-- rewrtie evaluateMonad as evaluateM

#eval evalueteMonad (applyPrimeU applyDivOption) (applyPrimO applyDivOption) twoPlusThree
#eval evalueteMonad (applyPrimeU applyDivExcept) (applyPrimO applyDivExcept) twoPlusThree
-- well... because of the name and polymorphic applyPrimeU applyPrimeO, now its longer...
--

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div
