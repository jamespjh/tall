-- Proofs from chapter 2 of "Foundations of Mathametics by Stewart and Tall".

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.Basic

-- note that the naive interpretation of integer division is closest to "lifting to rationals"
-- if we had truncating integer division, it wouldn't be true.
theorem rearrange_equation (a b c: ℕ) : b ≠ 0 ∧ (a: ℚ) / b = c → a=b * c := by
    intro ht
    rcases ht with ⟨ hb, ha ⟩
    field_simp [hb] at ha
    norm_cast at ha

#print rearrange_equation

-- We will end up proving there's a common factor of p and q
-- we would then need the fact that thus we can divide it out, creating new p and q
-- this would be able to continue forever which doesn't make sense
theorem tower_means_fail (f : Nat -> Prop) (hyp : ∀ p: ℕ,
  f p -> ∃ n, n < p ∧ f n) : ∀ k, ¬ f k := by
  intro k hk
  induction' k using Nat.strong_induction_on with l ih
  have hyp2 := hyp l hk
  rcases hyp2 with ⟨ z, hlt, hzf ⟩
  exact ih z hlt hzf

theorem tower_or_zero (f : Nat -> Prop) (hyp :  ∀ p: ℕ, 0 < p ∧ f p -> (∃ m, m < p ∧ 0 < m ∧ f m )) : ∀ k, f k -> k = 0 := by
  intro k hk
  have hh := tower_means_fail (fun n =>  0 < n ∧ f n) hyp k
  sorry

theorem half_is_a_tower (f : Nat -> Prop) (hyp : ∀ p: ℕ, f p -> (2 ∣ p) ∧ f (p/2)) : ∀ k,f k -> k=0 := by
  have htmz : ∀ p: ℕ, 0 < p ∧ f p -> (∃ m, m < p ∧ 0 < m ∧ f m ):= by
    intro p olp
    rcases olp with ⟨ a, b ⟩
    have h2 := hyp p b
    rcases h2 with ⟨ c, d ⟩
    use p/2
    constructor
    · apply Nat.div_lt_self a (by decide)
    constructor
    have kk : 2 ≤ p := Nat.le_of_dvd a c
    . apply Nat.div_pos kk (by decide)
    . exact d
  exact tower_or_zero f htmz


def are_rational_root_two (p q : ℕ) : Prop :=
  q ≠ 0 ∧ ((p : ℚ) / q) ^ 2 = 2

theorem tower_of_rationals (p q : ℕ): are_rational_root_two p q → ∃ (x y : ℕ), x = p/2 ∧ y = p/2 ∧ are_rational_root_two x y   := by
  intro h

  -- Assume x = p/q in lowest terms
  rcases h with ⟨ p, q, nz, h ⟩
  have h1 : p^2 = 2 * q^2 := by
    field_simp [nz] at h
    norm_cast at h
