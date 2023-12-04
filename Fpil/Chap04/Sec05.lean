import Fpil.Chap04.Sec04

-- # Standard Classes

-- # Equality and Ordering

#eval "Octopus" == "Cuttlefish"
#eval "Octopodes" == "Octo".append "podes"

-- #eval (fun x : Nat => 1 + x) == (Nat.succ ·)

#check (fun x : Nat => 1 + x) = (Nat.succ ·)
#check 2 < 4

-- #eval if (fun (x : Nat) => 1 + x) = (Nat.succ ·) then "yes" else "no"

-- inductive Ordering where
-- | lt
-- | eq
-- | gt

deriving instance Repr for Ordering

def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k


instance : Ord Pos where
  compare := Pos.comp


#check compare (5 : Pos) 3
#eval compare (5 : Pos) 3
#eval compare (5 : Pos) 5
#eval compare (4 : Pos) 5

-- # Hashing

-- class Hashable (α : Type) where
--   hash : α → UInt64

def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos

#eval hash (42 : Pos)

instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

#eval hash idahoSpiders

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf => true
  | BinTree.branch l1 x1 r1, BinTree.branch l2 x2 r2 =>
    x1 == x2 && eqBinTree l1 l2 && eqBinTree r1 r2
  | _, _ => false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf => 0
  | BinTree.branch l _ r =>
    mixHash 1 (mixHash (hashBinTree l) (hashBinTree r))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

def bTree1 : BinTree Pos := BinTree.leaf
def bTree2 : BinTree Pos := BinTree.branch BinTree.leaf 10 (BinTree.branch BinTree.leaf 5 BinTree.leaf)
def bTree3 : BinTree Pos := BinTree.branch (BinTree.branch BinTree.leaf 3 BinTree.leaf) 4 (BinTree.branch BinTree.leaf 5 BinTree.leaf)

deriving instance BEq for Pos

#eval bTree1 == bTree1
#eval bTree2 == bTree3
#eval hash bTree1
#eval hash bTree3

-- # Deriving Standard Classes

deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable, Repr for NonEmptyList

-- # Appending

-- class HAppend (α : Type) (β : Type) (γ : outParam Type) where
--   hAppend : α → β → γ

instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

#eval idahoSpiders ++ idahoSpiders

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys :=
    { head := xs.head, tail := xs.tail ++ ys }

#eval idahoSpiders ++ ["Trapdoor Spider", "Hoge Spider"]


-- # Functors

#eval Functor.map (· + 5) [1, 2, 3]
#eval (· + 5) <$> [1, 2, 3]

#eval Functor.map toString (some (List.cons 5 List.nil))
#eval toString <$> (some $ List.cons 5 List.nil)

#eval Functor.map List.reverse [[1, 2, 3], [4, 5, 6]]
#eval List.reverse <$> [[1, 2, 3], [4, 5, 6]]

instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }

#eval (· ++ " kumo") <$> idahoSpiders

instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }


def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | z :: zs => catList (start ++ z) zs
  catList xs.head xs.tail

#eval concat idahoSpiders

-- class Functor (f : Type → Type) where
--   map : {α β : Type} → (α → β) → f α → f β

--   mapConst {α β : Type} (x : α) (coll : f β) : f α :=
--     map (fun _ => x) coll

-- # Exercises

def BinTree.map (f : α → β) : BinTree α → BinTree β
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l x r =>
    BinTree.branch (BinTree.map f l) (f x) (BinTree.map f r)

instance : Functor BinTree where
  map := BinTree.map


def BinTree.toString [ToString α] : BinTree α → String
  | BinTree.leaf => "<Leaf>"
  | BinTree.branch l x r =>
    s!"({toString l}) " ++ s!"{x}" ++ s!" ({toString r})"

instance : ToString (BinTree Pos) where
  toString := BinTree.toString

#eval bTree1
#eval (· * (2 : Pos)) <$> bTree1

#eval bTree3
#eval (· * (2 : Pos)) <$> bTree3
