import Fpil.Chap04.Sec05

-- # Coercions

#check Pos.toNat


-- class Coe (α : Type) (β : Type) where
--   coe : α → β

instance : Coe Pos Nat where
  coe x := x.toNat

#eval [1, 2, 3, 4].drop (2 : Pos)
#check [1, 2, 3, 4].drop (2 : Pos)

-- # Chaining Coercions

def oneInt : Int := Pos.one

inductive A where
  | a

inductive B where
  | b

instance : Coe A B where
  coe _ := B.b

instance : Coe B A where
  coe _ := A.a

instance : Coe Unit A where
  coe _ := A.a

def coercedToB : B := ()

deriving instance Repr for B
#eval coercedToB

def List.last? : List α → Option α
  | [] => none
  | [x] => x -- some x
  | _ :: x :: xs => last? (x :: xs)

#eval List.last? [1,2,3]

def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"

#eval perhapsPerhapsPerhaps

-- def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
--   392

def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  ↑(392 : Nat)

#eval perhapsPerhapsPerhapsNat


-- # Non-Empty Lists and Dependent Coercions

instance : Coe (NonEmptyList α) (List α) where
  coe
    | { head := x, tail := xs } => x :: xs

-- class CoeDep (α : Type) (x : α) (β : Type) where
--   coe : β

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs}

-- # Coercing to Types

structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }



def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs


instance : CoeSort Monoid Type where
  coe m := m.Carrier

def foldMap' (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

instance : CoeSort Bool Prop where
  coe b := b = true

-- # Coercing to Functions
