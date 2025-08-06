-- Proofs from chapter 2 of "Foundations of Mathametics by Stewart and Tall".

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.Basic


theorem rearrange_equation  (x: ℚ) (c: ℕ) : 0 ≤ x ∧ x = c → ∃ (a: ℕ )(b: ℕ), a=c * b := by
    intro ht
    obtain ⟨hc, h⟩ := ht
  -- Extract numerator and denominator:
  -- AI gave below
      -- Numerator and denominator of x
    let nz := x.num
    let n := nz.toNat
    let d := x.den
    have dnz : d ≠ 0 := x.den_nz

    have nnz: n = nz := by
      have nzg : 0 ≤ nz := x.num_nonneg.mpr hc
      exact @Int.toNat_of_nonneg x.num nzg
    have nnnz: (n: ℚ) = nz := by
      norm_cast

    -- Replace x with n / d (this is just the definition of Rat)
    have h' : (n : ℚ ) / d = c := by
      rw [<- Rat.num_div_den x] at h
      rw [nnnz]
      exact h

    -- Now we can rearrange the equation
    have h_mul : n  =  c * (d : ℚ) :=
      Eq.symm ((div_eq_iff_mul_eq (Nat.cast_ne_zero.mpr dnz)).mp h')
    norm_cast at h_mul
    use n, d
    --norm_cast at h_mul

theorem root_2_irrational : ¬∃ (p q : ℤ), q ≠ 0 ∧ (p / q) ^ 2 = 2 := by
  intro h

  -- Assume x = p/q in lowest terms
  rcases h with ⟨ n, d, nz, co ⟩
  have h1 : n = 2 * d := by
