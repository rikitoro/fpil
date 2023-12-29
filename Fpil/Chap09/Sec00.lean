-- # Interlude : Tactics, Induction, and Proofs
import Fpil.Util.BinTree

def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => plusL n k + 1

def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1

-- # The Induction Tactic

theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rw [←ih]

-- # Tactic Golf

theorem plusR_zero_left' (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
    assumption

theorem plusR_zero_left'' (k : Nat) : k = Nat.plusR 0 k := by
  induction k
  case zero => simp [Nat.plusR]
  case succ n ih =>
    simp [Nat.plusR]
    assumption

theorem plusR_zero_left''' (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR] <;> assumption

-- # Induction on Other Datatypes
