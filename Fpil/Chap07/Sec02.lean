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
