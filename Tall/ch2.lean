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

def are_rational_root_two (p q : ℕ) : Prop :=
  0 < q ∧ ((p : ℚ) / q) ^ 2 = 2

theorem tower_of_rationals (p q : ℕ): are_rational_root_two p q → ∃ (x y : ℕ), 2 * x = p ∧ 2 * y = q ∧ are_rational_root_two x y   := by
  intro h
  rcases h with ⟨ qnz, h ⟩
  have h1 : p^2 =  2 * q^2 := by
    field_simp [qnz] at h
    norm_cast at h
    rw [h]
    ring
  have ep2 : Even (p^2) := by
    use q^2
    rw [h1]
    ring
  have ep : Even p := by
    rw [pow_two] at ep2
    have a2 := Nat.even_mul.mp ep2
    rcases a2 with a | a
    exact a; exact a
  let x := p / 2
  have h3: p = 2 * x := by
    rw [Nat.mul_div_cancel' (Even.two_dvd ep)]
  have h4 : (2 * q ^ 2 = 2 * (2 * x * x)) := by
    rw [h3] at h1
    ring_nf at h1
    ring_nf
    rw [h1]
  have h5: q ^ 2 = 2 * x * x := by
    apply Nat.mul_left_cancel (by decide) h4
  have eq2 : Even (q^2) := by
    use x * x
    rw [h5]
    ring
  have eq : Even (q) := by
    rw [pow_two] at eq2
    have a2 := Nat.even_mul.mp eq2
    rcases a2 with a | a
    exact a; exact a
  let y := q / 2
  have h6: q = 2 * y := by
    rw [Nat.mul_div_cancel' (Even.two_dvd eq)]
  have h7 : x^2 = 2 * y^2 := by
    rw [h3, h6] at h1
    ring_nf at h1
    have exp4: x ^ 2 * 4 = (y ^ 2 * 2) * 4 := by
      rw [h1]
      ring
    rw [Nat.mul_right_cancel (by decide) exp4]
    ring
  have ynz : 0 < y := by
    rw [h6] at qnz
    exact Nat.pos_of_mul_pos_left qnz
  use x, y
  constructor
  rw [h3]
  constructor
  rw [h6]
  constructor
  exact ynz
  field_simp [ynz]
  norm_cast
  rw [h7]
  ring

def part_of_root_of_two (n : ℕ) : Prop :=
  ∃ p : ℕ, are_rational_root_two p n

theorem part_implies_tower (n : ℕ) : part_of_root_of_two n -> ∃ m < n, part_of_root_of_two m := by
  intro h
  unfold part_of_root_of_two at h
  rcases h with ⟨ p, hp ⟩
  have tower := tower_of_rationals p n hp
  rcases tower with ⟨ x, y, hx1, hy1, hy2 ⟩
  use y
  constructor
  unfold are_rational_root_two at hp
  rcases hp with ⟨ nnz, _ ⟩
  have ynz : 0 < y := by
    rw [<-hy1] at nnz
    exact Nat.pos_of_mul_pos_left nnz
  -- use lemma for a * b = c -> a ≤ c
  rw [<-hy1]
  have a: 1 < 2 := by decide
  have b := Nat.mul_lt_mul_of_pos_left (a) ynz
  rw [Nat.mul_one] at b
  ring_nf
  exact b
  unfold part_of_root_of_two
  use x

theorem no_rational_root_of_two (a b : ℕ): ¬ are_rational_root_two a b := by
  intro h
  have prb: part_of_root_of_two b := by
    unfold part_of_root_of_two
    use a
  have problem := (tower_means_fail part_of_root_of_two part_implies_tower)
  have contra := problem b prb
  contradiction
