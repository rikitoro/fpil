-- import Fpil.Chap05.Sec00
import Fpil.Chap04.Sec05 -- BinTree

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

def ok (x : α) : State σ α :=
  fun s => (s, x)

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def increment (howMuch : Int) : State Int Int :=
  get >>= fun i =>
  set (i + howMuch) >>= fun () =>
  pure i

#eval mapM increment [1, 2, 3, 4, 5] 100

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes } := result
    let {log := nextOut, val := nextRes } := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}

def isEven (i : Int) : Bool :=
  i % 2 == 0

def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then
    save i
    else pure ()) >>= fun () =>
  pure i

deriving instance Repr for WithLog

#eval mapM saveIfEven [1, 2, 3, 4 , 5]

-- # The Identity Monad

-- def Id (t : Type) : Type := t

instance : Monad Id where
  pure x := x
  bind x f := f x

#eval mapM (m := Id) (· + 1) [1, 2, 3, 4, 5]

-- #eval mapM (· + 1) [1, 2, 3, 4, 5]

-- #eval mapM (fun x => x) [1, 2, 3, 4]

-- # The Monad Contract

-- bind (pure v) f = f v
-- bind v pure = v
-- bind (bind v f) g = bind v (fun x => bind (f x) g)

-- # Exercises

-- ## Mapping on a Tree

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | BinTree.leaf => pure BinTree.leaf
  | BinTree.branch l x r =>
    mapM f l >>= fun ml =>
    f x >>= fun mx =>
    mapM f r >>= fun mr =>
    pure $ BinTree.branch ml mx mr

def bTree4 : BinTree Int :=
  BinTree.branch (BinTree.branch BinTree.leaf 2 BinTree.leaf) 5 (BinTree.branch BinTree.leaf 10 BinTree.leaf)

deriving instance Repr for BinTree

#eval bTree4
#eval BinTree.mapM increment bTree4 0
#eval BinTree.mapM saveIfEven bTree4

-- ## The Option Monad Contract
