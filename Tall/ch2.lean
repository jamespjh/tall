-- Proofs from chapter 2 of "Foundations of Mathametics by Stewart and Tall".

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.Basic


theorem rearrange_equation  (x: ℚ) (c: ℕ) : 0 ≤ x ∧ x = c → ∃ (a: ℕ )(b: ℕ), a=c * b := by
    intro ht

    use x.num.toNat, x.den

    simp [*] at *


theorem root_2_irrational : ¬∃ (p q : ℤ), q ≠ 0 ∧ (p / q) ^ 2 = 2 := by
  intro h

  -- Assume x = p/q in lowest terms
  rcases h with ⟨ n, d, nz, co ⟩
  have h1 : n = 2 * d := by
