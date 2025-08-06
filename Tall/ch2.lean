-- Proofs from chapter 2 of "Foundations of Mathametics by Stewart and Tall".

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.Basic


theorem rearrange_equation  (x: ℚ) (c: ℕ) : 0 ≤ x ∧ x = c → ∃ (a: ℕ )(b: ℕ), a=c * b := by
    intro ht
    obtain ⟨zltx, h⟩ := ht

    let nq := (x.num : ℚ ) -- we have to work in Q to be able to use
    let dq := (x.den : ℚ)        -- theorems on multiplying up.

    have dqnz : dq ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz

    -- Now we're in Q and can rearrange the equation
    -- using num_div_den for the definition of rational numbers.
    have h_mul : nq =  c * dq := by
      rw [<- Rat.num_div_den x] at h
      field_simp [dqnz] at h
      assumption


    -- the critical thing we need to prove is that nq = x.num.toNat
    have nnnz: nq = x.num.toNat := by
      dsimp [nq]
      have nnz: x.num = x.num.toNat := by
        simp [Int.toNat_of_nonneg, x.num_nonneg]
        assumption
      norm_cast

    use x.num.toNat, x.den

    dsimp [nq,dq] at h_mul
    norm_cast at h_mul
    simp only [h_mul, nnnz]
    norm_cast


theorem root_2_irrational : ¬∃ (p q : ℤ), q ≠ 0 ∧ (p / q) ^ 2 = 2 := by
  intro h

  -- Assume x = p/q in lowest terms
  rcases h with ⟨ n, d, nz, co ⟩
  have h1 : n = 2 * d := by
