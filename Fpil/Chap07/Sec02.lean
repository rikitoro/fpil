-- # A Monad Cnstruction Kit

-- # Failure with OPtionT

-- def OptionT (m : Type u → Type v) (α : Type u) : Type v :=
--   m (Option α)

def getSomeInput : OptionT IO String := do
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trim
  if trimmed == "" then
    failure
  else pure trimmed

structure UserInfo where
  name : String
  favoriteBeetle : String

def getUserInfo : OptionT IO UserInfo := do
  IO.println "What is your name?"
  let name ← getSomeInput
  IO.println "What if your favorite species of beetle?"
  let beetle ← getSomeInput
  pure ⟨name, beetle⟩

def interact : IO Unit := do
  match ← getUserInfo with
  | none => IO.eprintln "Missing info"
  | some ⟨name, beetle⟩ => IO.println s!"hello {name}, whose favorite beettle is {beetle}"

instance [Monad m] : Monad (OptionT m) where
  pure x := (pure (some x) : m (Option _))
  bind action next := (do
    match (← action) with
    | none => pure none
    | some v => next v : m (Option _))

-- structure OptionT (m : Type u → Type v) (α : Type y) :
--   Type v where
--   run : m (Option α)

-- def OptionT.mk (x : m (Option α)) : OptionT m α := x
-- def OptionT.run (x : OptionT m α) : m (Option α) := x

instance [Monad m] : Monad (OptionT m) where
  pure x := OptionT.mk $ pure $ some x
  bind action next := OptionT.mk do
    match ← action with
    | none => pure none
    | some v => next v


-- # An Alternative Instance

instance [Monad m] : Alternative (OptionT m) where
  failure := OptionT.mk $ pure none
  orElse x y := OptionT.mk do
    match ← x with
    | some result => pure $ some result
    | none => y ()

-- # Lifting

instance [Monad m] : MonadLift m (OptionT m) where
  monadLift action := OptionT.mk do
    pure $ some $ ← action

-- # Exceptions

-- def ExceptT (ε: Type u) (m : Type u → Type v) (α : Type u) : Type v :=
--   m (Except ε α)

-- def ExceptT.mk {ε α : Type u} (x : m (Except ε α)) : ExceptT ε m α := x
-- def ExceptT.run {ε α : Type u} (x : ExceptT ε m α) : m (Except ε α) := x

instance {ε : Type u} {m : Type u → Type v} [Monad m] : Monad (ExceptT ε m) where
  pure x := ExceptT.mk $ pure $ Except.ok x
  bind result next := ExceptT.mk do
    match ← result with
    | .error e => pure $ .error e
    | .ok x => next x

instance [Monad m] : MonadLift (Except ε) (ExceptT ε m) where
  monadLift action := ExceptT.mk (pure action)

instance [Monad m] : MonadLift m (ExceptT ε m) where
  monadLift action := ExceptT.mk (.ok <$> action)

-- # Type Classes for Exceptions

-- class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where
--   throw : ε → m α
--   tryCatch : m α → (ε → m α) → m α

-- inductive Err where
--   | divByZero
--   | notANumber : String → Err

inductive Err where
  | divByZero
  | notANumber : String → Err

def divBackend [Monad m] [MonadExcept Err m] (n k : Int) : m Int :=
  if k == 0 then
    throw .divByZero
  else pure (n / k)

def asNumber [Monad m] [MonadExcept Err m] (s : String) : m Int :=
  match s.toInt? with
  | none => throw (.notANumber s)
  | some i => pure i

def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  tryCatch (do pure $ toString (← divBackend (← asNumber n) (← asNumber k)))
    fun
    | .divByZero => pure "Division By zero!"
    | .notANumber s => pure s!"Not a number: \"{s}\""

def divFrontend' [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  try
    pure $ toString $ ← divBackend (← asNumber n) (← asNumber k)
  catch
    | .divByZero => pure "Division by zero!"
    | .notANumber s => pure s!"Not a number: \"{s}\""


-- # State

-- def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
--   σ → m (α × σ)

instance [Monad m] : Monad (StateT σ m) where
  pure x := fun s => pure (x, s)
  bind result next := fun s => do
    let (v, s') ← result s
    next v s'

structure LetterCounts where
  vowels : Nat
  consonants : Nat
deriving Repr

inductive Err' where
  | notALetter : Char → Err'
deriving Repr

def vowels :=
  let lowerVowels := "aeiuoy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper)

def countLetters (str : String) : StateT LetterCounts (Except Err') Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      let st ← get
      let st' ←
        if c.isAlpha then
          if vowels.contains c then
            pure {st with vowels := st.vowels + 1}
          else if consonants.contains c then
            pure {st with consonants := st.consonants + 1}
          else
            pure st
        else throw (.notALetter c)
      set st'
      loop cs
  loop str.toList


-- class MonadState (σ : outParam (Type u)) (m : Type u → Type v) : Type (max (u + 1) w) where
--   get : m σ
--   set : σ → m PUnit
--   modifyGet : (σ → α × σ) → m α

-- def modify [MonadState σ m] (f : σ → σ) : m Unit :=
--   modifyGer fun s => ((), f s)
