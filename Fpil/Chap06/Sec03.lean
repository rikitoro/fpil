import Fpil.Chap06.Sec02

-- # The Applicative Contract

-- 1. pure id <*> v = v
-- 2. pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)
-- 3. pure f <*> pure x = pure (f x)
-- 4. u <*> x = pure (fun f => f x) <*> u

-- # All Applicatives are Functors

def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x

-- class Applicative (f : Type → Type) extends Functor f where
--   pure : α → f α
--   seq : f (α → β) → (Unit → f α) → f β
--   map g x := seq (pure g) (fun () => x)

-- # All Monads are Applicative Functors

-- # Additional Stipulations

def notFun : Validate String (Nat → String) :=
  .errors { head := "first error", tail := []}

def notArg : Validate String Nat :=
  .errors { head := "second error", tail := []}

#eval notFun <*> notArg

#eval notFun.andThen fun g => notArg.andThen fun y => pure (g y)
