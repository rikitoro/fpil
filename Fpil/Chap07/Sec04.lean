import Fpil.Util.LetterCounts

-- # More do Feasures

-- # Single-Branched if

def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        -- else
        --   pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList

def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    if ← p x then
      modify (· + 1)
    count p xs

def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    unless ← p x do
      modify (· + 1)
    countNot p xs

-- # Early Return

def List.find'? (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs =>
    if p x then
      some x
    else find'? p xs

def List.find''? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs => do
    if p x then return x
    find''? p xs

def runCatch [Monad m] (action : ExceptT α m α) : m α := do
  match ← action with
  | Except.ok x => pure x
  | Except.error x => pure x

def List.find'''? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs =>
    runCatch do
      if p x then throw x else pure ()
      monadLift (find'''? p xs)

def greet (name : String) : String :=
  "Hello, " ++ Id.run do return name

#eval greet "David"

-- # Loops

-- # Looping with ForM

-- class ForM (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) where
--   forM [Monad m] : γ → (α → m PUnit) → m PUnit

#print PUnit
-- PUnit is a version of the Unit type that is universe-polymorphic to allow it to be in Type u instead of Type.

-- def List.forM [Monad m] : List α → (α → m PUnit) → m PUnit
--   | [], _ => pure ()
--   | x :: xs, action => do
--     action x
--     forM xs action

-- instance : ForM m (List α) α where
--   forM := List.forM

def countLetters' (str : String) : StateT LetterCounts (Except Err) Unit :=
  forM str.toList fun c => do
    if c.isAlpha then
      if vowels.contains c then
        modify fun st => {st with vowels := st.vowels + 1}
      else if consonants.contains c then
        modify fun st => {st with consonants := st.consonants + 1}
    else throw (.notALetter c)

structure AllLessThan where
  num : Nat

def AllLessThan.forM [Monad m] (coll : AllLessThan) (action : Nat → m Unit) : m Unit :=
  let rec countdown : Nat → m Unit
    | 0 => pure ()
    | n + 1 => do
      action n
      countdown n
  countdown coll.num

instance : ForM m AllLessThan Nat where
  forM := AllLessThan.forM

#eval forM { num := 5 : AllLessThan} IO.println


-- # Stopping Iteration

def OptionT.exec [Applicative m] (action : OptionT m α) : m Unit :=
  action *> pure ()

def countToThree (n : Nat) : IO Unit :=
  let nums : AllLessThan := ⟨n⟩
  OptionT.exec $
    forM nums fun i => do
      if i < 3 then failure else IO.println i

#eval countToThree 7

instance : ForIn m AllLessThan Nat where
  forIn := ForM.forIn

def countToThree' (n : Nat) : IO Unit := do
  let nums : AllLessThan := ⟨n⟩
  for i in nums do
    if i < 3 then break
    IO.println i

#eval countToThree' 7

def List.find_? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if p x then return x
  failure

def num_list := [3, 1, 4, 1, 5, 9]
#eval num_list.find_? (fun x => x % 5 == 0)
#eval num_list.find_? (fun x => x % 7 == 0)

def List.find__? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if not (p x) then continue
    return x
  failure

#eval num_list.find__? (fun x => x % 5 == 0)
#eval num_list.find__? (fun x => x % 7 == 0)

#check [4:9:2]

def fourToEight : IO Unit := do
  for i in [4:9:2] do
    IO.println i

#eval fourToEight

def parallelLoop := do
  for x in ["currant", "gooseberry", "rowan"], y in [4 : 8] do
    IO.println (x, y)

#eval parallelLoop
