/- # Safe Array Indices -/

-- structure Fin (n : Nat) where
--   val : Nat
--   isLt : LT.lt val n

#eval (5 : Fin 10)
#eval (42 : Fin 10)


def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Fin arr.size × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (⟨i, h⟩, x)
    else findHelper arr p (i + 1)
  else none
termination_by findHelper arr p i => arr.size - i

def Array.find (arr : Array α) (p : α → Bool) : Option (Fin arr.size × α) :=
  findHelper arr p 0

#eval #[3, 1, 4, 1, 5, 9, 2, 4].find (fun n => n % 2 == 0)
#eval #[3, 1, 4, 1, 5, 9, 2, 4].find (fun n => n == 0)
