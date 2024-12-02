import Ch6.ApplicativeFunctor
-- There are four rules that an applicative functor should follow:

-- It should respect identity, so pure id <*> v = v
-- It should respect function composition, so pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)
-- Sequencing pure operations should be a no-op, so pure f <*> pure x = pure (f x)
-- The ordering of pure operations doesn't matter, so u <*> pure x = pure (fun f => f x) <*> u


-- All applicatives are Functors
def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x
-- This justifies a definition of Applicative that extends Functor,
class Applicative' (f : Type → Type) extends Functor f where
  pure : α → f α
  seq : f (α → β) → (Unit → f α) → f β
  map g x := seq (pure g) (fun () => x)


-- All Monads are Applicatives
-- in andthen style
def seq' [Monad m] (f : m (α → β)) (x : Unit → m α) : m β :=
  f >>= fun f' =>
  x () >>= fun x' =>
  pure (f' x')

-- in do style
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let f' ← f
  let x' ← x ()
  pure (f' x')


-- class Monad (m : Type → Type) extends Applicative m where
--   bind : m α → (α → m β) → m β
--   seq f x :=
--     bind f fun g =>
--     bind (x ()) fun y =>
--     pure (g y)
--
-- `Monad` has default `seq` and `map` definitions.
-- `Applicative`'s own default definition of `map` means that every `Monad` instance automatically generates `Applicative` and `Functor` instances as well.
def notFun : Validate String (Nat → String) :=
  .errors { head := "First error", tail := [] }

def notArg : Validate String Nat :=
  .errors { head := "Second error", tail := [] }
