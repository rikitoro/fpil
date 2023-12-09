import Fpil.Util.BinTree

-- # Additional Conveniences

-- # Shared Argument Types

def equal? [BEq α] (x y : α) : Option α :=
  if x == y then
    some x
  else
    none

#eval equal? 2 3
#eval equal? 2 2

-- # Leading Dot Notation

def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r =>
    .branch (mirror r) x (mirror l)

def btree1 : BinTree String :=
  .branch
    (.branch .leaf "AB" .leaf)
    "CD"
    (.branch
      (.branch .leaf "EF" .leaf)
      "GH"
      (.branch .leaf "IJ" .leaf)
    )

#eval btree1
#eval BinTree.mirror btree1

def BinTree.empty : BinTree α := .leaf

#check (.empty : BinTree Nat)


-- # Or-Patterns

inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr

def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false

#eval Weekday.isWeekend .saturday
#eval Weekday.isWeekend .wednesday

def condence : α ⊕ α → α
  | .inl x | .inr x => x

#eval condence (.inl 10 : Nat ⊕ Nat)
#eval condence (.inr 15 : Nat ⊕ Nat)

def stringy : Nat ⊕ Weekday → String
  | .inl x  | .inr x  => s!"It is {repr x}"

#eval stringy (.inl 10 : Nat ⊕ Weekday)
#eval stringy (.inr .monday : Nat ⊕ Weekday)

def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat
  | .inl (n, x) | .inr (n, y) => n

#eval getTheNat (.inl (10, "hoge") : (Nat × String) ⊕ (Nat × Float))
#eval getTheNat (.inr (5, 3.14) : (Nat × String) ⊕ (Nat × Float))

-- def getTheAlpha : (Nat × α) ⊕ (Nat × α) → α
--   | .inl (n, x) | .inr (n, y) => x

def str := "Some string"

def getTheString : (Nat × String) ⊕ (Nat × β) → String
  | .inl (n, str) | .inr (n, y) => str

#eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × String))

#eval getTheString (.inr (20, "twenty"))
