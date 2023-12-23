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
