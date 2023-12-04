import Fpil.Chap04.Sec02

-- # Arrays and Indexing

-- # Arrays

def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]

#eval northernTrees[2]
-- #check northernTrees[8]

-- # Non-Empty Lists

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

-- def NonEmptyList.get? : NonEmptyList α → Nat → Option α
--   | xs, 0 => some xs.head
--   | {head := _, tail := []}, _ + 1 => none
--   | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail.get? n

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by simp

theorem notSixSpiders : ¬ idahoSpiders.inBounds 5 := by simp

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]

-- # Overloading Indexing

-- class GetElem (coll : Type) (idx : Type) (item : outParam Type) (inBounds : outParam (coll → idx → Prop)) where
--   getElem : (c : coll) → (i : idx) → inBounds c i → item

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

#check idahoSpiders[0]
-- #check idahoSpiders[9]
#check idahoSpiders[0]?
#check idahoSpiders[9]?

instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y

#eval {x:= 1.2, y:=3.4 : PPoint Float}[true]
#eval {x:= 1.2, y:=3.4 : PPoint Float}[false]
