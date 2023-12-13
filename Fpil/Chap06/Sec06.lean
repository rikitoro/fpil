-- # The Complete Definitions

-- # Functor

-- class Functor (f : Type u → Type v) : Type (max (u + 1) v) where
--   map : {α β : Type u} → (α → β) → f α → f β
--   mapConst : {α β : Type u} → α → f β → f α :=
--     Function.comp map (Function.const _)

def simpleConst (x : α) (_ : β) : α := x

#eval [1, 2, 3].map (simpleConst "same")

-- class Functor (f : Type u → Type v) : Type (max (u + 1) v) where
--   map : {α β : Type u} → (α → β) → f α → f β

-- inductive Functor (f : Type u → Type v) : Type (max (u+1) v) where
--   | mk : ({α β : Type u} → (α → β) → f α → f β) → Functor f

-- # Applicative

-- class Pure (f : Type u → Type v) : Type (max (u + 1) v) where
--   pure {α : Type u} : α → f α

-- class Seq (f : Type u → Type v) : Type (max (u + 1) v) where
--   seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β

-- class SeqRight (f : Type u → Type v) : Type (max (u + 1) v) where
--   seqRight : {α β : Type u} → f α → (Unit → f β) → f β

-- class SeqLeft (f : Type u → Type v) : Type (max (u + 1) v) where
--   seqLeft : {α β : Type u} → f α → (Unit → f β) → f α
