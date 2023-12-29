/- # Arrays and Termination -/

-- ## Inequality

-- class LE (α : Type u) where
--   le : α → α → Prop

-- class LT (α : Type u) where
--   lt : α → α → Prop

instance : LE Nat where
  le := Nat.le

-- ## Inductively-Defined Propositions, Predicates, and Relations

inductive EasyToProve : Prop where
  | heresTheProof : EasyToProve

theorem fairlyEasy : EasyToProve := by
  constructor

-- inductive True : Prop where
--   | intro : True

inductive IsThree : Nat → Prop where
  | isThree : IsThree 3

theorem three_is_three : IsThree 3 := by
  constructor

inductive IsFive : Nat → Prop where
  | isFive : IsFive 5

theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => constructor

theorem four_is_not_three : ¬ IsThree 4 := by
  simp [Not]
  intro h
  cases h

-- inductive Nat.le (n : Nat) : Nat → Prop
--   | refl : Nat.le n n
--   | step : Nat.le n m → Nat.le n (m + 1)

theorem four_le_seven : 4 ≤ 7 :=
  open Nat.le in
  step $ step $ step refl

-- def Nat.lt (n m : Nat) : Prop :=
--   Nat.le (n + 1) m

instance : LT Nat where
  lt := Nat.lt

theorem four_lt_seven : 4 < 7 :=
  open Nat.le in
  step $ step refl

-- # Proving Termination
def arrayMapHelper (f : α → β) (arr : Array α) (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push $ f arr[i]) (i + 1)
  else soFar
termination_by arrayMapHelper _ arr _ i => arr.size - i

def  Array.map' (f : α → β) (arr : Array α) : Array β :=
  arrayMapHelper f arr Array.empty 0

#eval Array.map' (fun str => str.length) #["abc", "de", "f", ""]

def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if  p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
termination_by findHelper arr _ i => arr.size - i


def Array.find' (arr : Array α) (p : α → Bool) : Option (Nat × α) :=
  findHelper arr p 0

#eval (#["abc", "de", "f", ""]).find' (fun str => str.length == 2)
