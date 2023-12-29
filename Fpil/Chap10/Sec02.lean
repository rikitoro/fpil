import Fpil.Chap10.Sec01

-- # Proving Equivalence

-- ## Proving sum Equal


-- theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
--   n + Tail.sum xs = Tail.sumHelper n xs := by
--   induction xs with
--   | nil => rfl
--   | cons y ys ih =>
--   --  simp [Tail.sum, Tail.sumHelper]
--     sorry

theorem non_tail_sum_eq_helper_acumm (xs : List Nat) :
  (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [← Nat.add_assoc, Nat.add_comm y n]
    exact ih (n + y)

theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [← Nat.zero_add (NonTail.sum _)]
  exact non_tail_sum_eq_helper_acumm xs 0





-- theorem non_tail_sum_eq_tail_sum :
--   NonTail.sum = Tail.sum := by
--   funext xs
--   induction xs with
--   | nil => rfl
--   | cons y ys ih =>
--     simp [NonTail.sum, Tail.sum, Tail.sumHelper]
--     rw [ih]
--     sorry


-- unsolved goals

-- case h.cons
-- y: Nat
-- ys: List Nat
-- ih: NonTail.sum ys = Tail.sum ys
-- ⊢ y + Tail.sum ys = Tail.sumHelper y ys
