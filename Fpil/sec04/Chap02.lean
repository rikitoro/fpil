import Fpil.sec04.Chap01

-- # Type Classes and Polymorphism

-- # Checking Polymorphic Functions' Types

#check (IO.println)
#check @IO.println
-- # Defining Polymorphic Functions with Instance Implicits

def List.sum [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sum

def fourNats : List Nat := [1, 2, 3, 4]

#eval fourNats.sum

def fourPos : List Pos := [1, 2, 3, 4]

-- #eval fourPos.sum

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.x + p2.x }

-- # Methods and Implicit Arguments


-- # Exercises

-- ## Even Number Literals

instance : OfNat Even Nat.zero where
  ofNat := Even.zero

instance [OfNat Even n] : OfNat Even (n + 2) where
  ofNat :=
    Even.next $ OfNat.ofNat n


#eval (6 : Even) + 4
#check (6 : Even) + 4

#eval (6 : Even) * 4
#check (6 : Even) * 4

-- ## Recursive Instance Serch Depth

#eval (254 : Even)
#check (254 : Even)
-- #eval (256 : Even)
-- #check (256 : Even)
