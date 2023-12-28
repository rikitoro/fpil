-- # Pitfalls of Programming with Dependent Types
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)

def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => plusL n k + 1

def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1

-- def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
--   | .nil, ys => _
--   | .cons x xs, ys => _

-- # Definitional Equality

-- def apendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
--   | 0, k, .nil, ys => _
--   |  n + 1, k, .cons x xs, ys => _

-- def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
--   | 0, k, .nil, ys => (_ : Vect α k)
--   | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))

-- def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
--   | 0, k, .nil, ys => (ys : Vect α k)
--   | n + 1, k, .cons x xs, ys => .cons x (appendL n k xs ys)

def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (appendL xs ys)
