-- import Fpil.Chap05.Sec00

-- # The Monad Type Class

-- class Monad (m : Type → Type) where
--   pure : α → m α
--   bind : m α → (α → m β) → m β

instance : Monad Option where
  pure := some
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

instance : Monad (Except ε) where
  pure := Except.ok
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def slowMammals : List String :=
  ["Three-toed sloth", "slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]

#eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds

def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximun is {xs.length - 1})"
  | some x => Except.ok x

#eval firstThirdFifthSeventh getOrExcept slowMammals
#eval firstThirdFifthSeventh getOrExcept fastBirds

-- # General Monad Operation

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'
