-- # Universee

#check Prop

#check Type

-- # User Defined Types

-- inductive MyList (α : Type) : Type where
--   | nil : MyList α
--   | cons : α → MyList α → MyList α

-- def myListOfNat : MyList Type :=
--   .cons Nat .nil

-- inductive MyList (α : Type 1) : Type where
--   | nil : MyList α
--   | cons : α → MyList α → MyList α

-- # Universe Polymorphism

inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons : α → MyList α → MyList α

def myListOfNumbers : MyList Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNumbers' : MyList.{0} Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList Type :=
  .cons Nat (.cons Float .nil)

def myListOfNat' : MyList.{1} Type :=
  .cons Nat (.cons Float .nil)

def myListOfList : MyList (Type → Type) :=
  .cons MyList (.cons Option .nil)

def myListOfList' : MyList.{1} (Type → Type) :=
  .cons MyList.{0} (.cons Option.{0} .nil)

inductive Sum' (α : Type u) (β : Type u) : Type u where
  | inl : α → Sum' α β
  | inr : β → Sum' α β

def stringOrNat : Sum' String Nat := .inl "Hello"

def typeOrType : Sum' Type (Type → Type) := .inr Option

-- def stringOrType : Sum' String Type := .inr Nat

-- # Prop and Polymorphism

def someTruePropositions : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "World!" = "Hello, world!"
]
