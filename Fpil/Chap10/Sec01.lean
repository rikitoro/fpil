-- # Tail Recursion

def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

#eval NonTail.sum [1, 2, 3]

def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs

#eval Tail.sum [1, 2, 3]

-- # Reversing Lists

def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

#eval NonTail.reverse [1, 2, 3]

def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs

#eval Tail.reverse [1, 2, 3]
