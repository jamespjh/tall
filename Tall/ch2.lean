-- Proofs from chapter 2 of "Foundations of Mathametics by Stewart and Tall".

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.Basic

-- note that the naive interpretation of integer division is closest to "lifting to rationals"
theorem rearrange_equation (a b c: ℕ) : b ≠ 0 ∧ (a: ℚ) / b = c → a=c * b := by
    intro ht
    rcases ht with ⟨ hb, ha ⟩
    field_simp [hb] at ha
    norm_cast at ha

#print rearrange_equation


theorem root_2_irrational : ¬∃ (p q : ℤ), q ≠ 0 ∧ (p / q) ^ 2 = 2 := by
  intro h

  -- Assume x = p/q in lowest terms
  rcases h with ⟨ n, d, nz, co ⟩
  have h1 : n = 2 * d := by
