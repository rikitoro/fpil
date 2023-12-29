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

def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r =>
    1 + l.count + r.count

def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

def BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l _ r ihl ihr =>
    simp_arith [BinTree.mirror, BinTree.count, ihl, ihr]

def BinTree.mirror_count' (t : BinTree α) : t.mirror.count = t.count := by
  induction t <;> simp_arith [BinTree.mirror, BinTree.count, *]
