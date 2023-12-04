-- # Positive Numbers

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

-- def seven : Pos := 7

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

-- def fourteen : Pos := seven + seven


-- # Classes and Instances

class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

open Plus (plus)

#eval plus 5 3

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ $ n.plus k

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos := plus seven seven


-- # Overloaded Addition

instance : Add Pos where
  add := Pos.plus

def fourteen' : Pos := seven + seven


-- Conversion to Strings

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

instance : ToString Pos where
  toString := posToString true

#eval s!"There are {seven}"

def Pos.toNat : Pos → Nat
| Pos.one => 1
| Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

#eval s!"There are {seven}"


-- # Overloaded Multiplication

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul

#eval [seven * Pos.one, seven * seven, Pos.succ Pos.one * seven]


-- # Literal Numbers

inductive LT4 where
  | zero
  | one
  | two
  | three
deriving Repr

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4)
#eval (0 : LT4)
-- #eval (4 : LT4)

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ $ natPlusOne k
    natPlusOne n

def eight : Pos := 8
-- def zero : Pos := 0


-- # Exercise

-- ## Another Representation

structure Pos' where
  succ ::
  pred : Nat

def Pos'.add : Pos' → Pos' → Pos'
| succ p, succ q => succ ∘ Nat.succ $ p + q

instance : Add Pos' where
  add := Pos'.add

def Pos'.mul : Pos' → Pos' → Pos'
| succ p, succ q => succ $ Nat.succ p * Nat.succ q

instance : Mul Pos' where
  mul := Pos'.mul

def Pos'.toNat : Pos' → Nat
| succ p => Nat.succ p

instance : ToString Pos' where
  toString := toString ∘ Pos'.toNat

instance : OfNat Pos' (n + 1) where
  ofNat := Pos'.succ n

#eval (1 : Pos')
#eval (42 : Pos')
-- #eval (0 : Pos')

#eval (1 : Pos') + 42
#check (1 : Pos') + 42

#eval (3 : Pos') * 42

-- ## Even Numbers

inductive Even where
| zero : Even
| next : Even → Even

def Even.add : Even → Even → Even
| Even.zero, e => e
| Even.next p, e => Even.next $ p.add e

instance : Add Even where
  add := Even.add

def Even.mul : Even → Even → Even
| Even.zero, _ => Even.zero
| Even.next p, e => e + e + p.mul e

instance : Mul Even where
  mul := Even.mul

def Even.toNat : Even → Nat
| Even.zero => 0
| Even.next p => 2 + toNat p

instance : ToString Even where
  toString := toString ∘ Even.toNat

def Even.four := Even.next $ Even.next Even.zero

#eval Even.zero
#eval Even.four + Even.four
#eval Even.four * Even.zero
#eval Even.four * Even.four

-- ## HTTP Requests
