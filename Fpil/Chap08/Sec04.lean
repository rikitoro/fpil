-- # Indices, Parameters, and Universe Levels

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

inductive WithParameter (α : Type u) : Type u where
  | test : α → WithParameter α

inductive WithTwoParamters (α : Type u) (β : Type v) : Type (max u v) where
  | test : α → β → WithTwoParamters α β

inductive WithParameterAfterColon : Type u → Type u where
  | test : α → WithParameterAfterColon α

inductive WithParameterAfterColon2 : Type u → Type u where
  | test1 : α → WithParameterAfterColon2 α
  | test2 : WithParameterAfterColon2 α

inductive WithParameterAfterColonDifferentNames : Type u → Type u where
  | test1 : α → WithParameterAfterColonDifferentNames α
  | test2 : β → WithParameterAfterColonDifferentNames β

-- inductive WithParameterBeforeColonDifferentNames (α : Type u) : Type u where
--   | test1 : α → WithParameterBeforeColonDifferentNames α
--   | test2 : β → WithParameterBeforeColonDifferentNames β
-- --
-- inductive datatype parameter mismatch
--   β
-- expected
--   α

-- inductive WithNamedIndex (α : Type u) : Type (u + 1) where
--   | test1 : WithNamedIndex α
--   | test2 : WithNamedIndex α → WithNamedIndex α → WithNamedIndex (α × α)
-- --
-- inductive datatype parameter mismatch
--   α × α
-- expected
--   α

inductive WithIndex : Type u → Type (u + 1) where
  | test1 : WithIndex α
  | test2 : WithIndex α → WithIndex α → WithIndex (α × α)

-- inductive ParamAfterIndex : Nat → Type u → Type u where
--   | test1 : ParamAfterIndex 0 γ
--   | test2 : ParamAfterIndex n γ → ParamAfterIndex k γ → ParamAfterIndex (n + k) γ

-- inductive NatParam (n : Nat) : Nat → Type u where
--   | five : NatParam 4 5

inductive NatParam (n : Nat) : Nat → Type u where
  | five : NatParam n 5

#print NatParam
#print Vect
