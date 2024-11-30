import Ch5.MonadArithmetic

#print evaluateM
#check Prim

namespace doStyle
def applyPrimReaderdo (op : String) (x : Int) (y : Int) : Reader Env Int := do
  let env ← read
  match env.lookup op with
  | none => Reader.pure 0
  | some f => Reader.pure (f x y)


-- same as applyPrim
def applyPrimdo [Monad m] (applySpecialdo : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, v1, v2 => applySpecialdo op v1 v2

-- rewrite evaluateM do in do-style
def evaluateMdo [Monad m] (applySpecialdo : special → Int → Int → m Int) : Expr (Prim special) → m Int
  | Expr.const n => pure n
  | Expr.unode _ _ => pure 0
  | Expr.prim op e1 e2 => do
    let v1 ← evaluateMdo applySpecialdo e1
    let v2 ← evaluateMdo applySpecialdo e2
    applyPrimdo applySpecialdo op v1 v2

-- check
open Expr Prim in
#eval evaluateMdo applyPrimReaderdo (prim (other "max") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) exampleEnv
end doStyle
