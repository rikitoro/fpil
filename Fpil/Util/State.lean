def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def State.ok (x : α) : State σ α := pure x

def State.get : State σ σ := fun s => (s, s)

def State.set (s : σ) : State σ Unit := fun _ => (s, ())

def State.andThen
  (first : State σ α) (next : α → State σ β) :
  State σ β :=
  first >>= next
