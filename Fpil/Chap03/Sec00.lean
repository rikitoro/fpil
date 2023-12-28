-- Interlude: Propositions, Proofs, and Indexing

def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]

-- def oops := woodlandCritters[3]

-- # Propositions and Proofs

def onePlusOneIsTwo : 1 + 1 = 2 := rfl

-- def onePlusOneIsFifteen : 1 +1 = 15 := rfl
-- --
-- type mismatch
--   rfl
-- has type
--   1 + 1 = 1 + 1 : Prop
-- but is expected to have type
--   1 + 1 = 15 : Prop

def OnePlusOneIsTwo : Prop := 1 + 1 = 2

theorem onePlusOneIsTwo' : OnePlusOneIsTwo := rfl

-- # Tactics

theorem onePlusOneIsTwo'' : 1 + 1 = 2 := by
  simp

-- # Connectives

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by simp

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by simp
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by simp
theorem trueIsTrue : True := True.intro
theorem trueOrFalse : True ∨ False := by simp
theorem falseImpliesTrue : False → True := by simp


-- # Evidence as Arguments

-- def third (xs : List α) : α := xs[2]

def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

#eval third woodlandCritters (by simp)

-- # Indexing Without Evidence

def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woodlandCritters

#eval thirdOption ["only", "two"]

#eval woodlandCritters[1]!
