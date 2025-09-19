-- Proofs from chapter 2 of "Foundations of Mathametics by Stewart and Tall".

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.Basic

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
  0 < q ∧ p ^ 2 = q ^ 2 * 2

lemma even_square (n : ℕ) : Even (n^2) → Even n := by
  intro h
  rw [pow_two] at h
  have a := Nat.even_mul.mp h
  rcases a with a | a
  exact a; exact a

lemma half_twice (n : ℕ) (hn : Even n) :  n =  (n/2) * 2:= by
  rw [Nat.mul_comm, Nat.mul_div_cancel' (Even.two_dvd hn)]

theorem tower_of_rationals (p q : ℕ):
    are_rational_root_two p q → ∃ (x y : ℕ),
    x * 2 = p ∧
    y * 2 = q ∧
    are_rational_root_two x y := by
  intro h
  rcases h with ⟨ qnz, h ⟩
  have ep2 : Even (p^2) := by
    use q^2
    rw [h]
    ring
  let x := p / 2
  have px2: p = x * 2 := half_twice p (even_square p ep2)
  have q2e : q ^ 2 = x ^ 2 * 2 := by
    rw [px2] at h
    ring_nf at h
    have : q ^ 2 * 2 = (x ^ 2 * 2) * 2 := by rw [<-h]; ring
    exact Nat.mul_right_cancel (by decide) this
  have eq2 : Even (q^2) := by
    use x ^ 2
    rw [q2e]
    ring
  let y := q / 2
  have qy2: q = y * 2 := half_twice q (even_square q eq2)
  use x, y
  unfold are_rational_root_two
  refine ⟨?a, ?b, ?y_positive ,?x_y_root⟩
  . exact px2.symm
  . exact qy2.symm
  . rw [qy2] at qnz
    exact Nat.pos_of_mul_pos_right qnz
  . ring_nf
    rw [px2, qy2] at h
    ring_nf at h
    have : x ^ 2 * 4 = (y ^ 2 * 2) * 4 := by rw [h]; ring
    exact Nat.mul_right_cancel (by decide) this

def part_of_root_of_two (n : ℕ) : Prop :=
  ∃ p : ℕ, are_rational_root_two p n

theorem part_implies_tower (n : ℕ) :
    part_of_root_of_two n -> ∃ m < n,
    part_of_root_of_two m := by
  intro h
  unfold part_of_root_of_two at h
  rcases h with ⟨ p, hp ⟩
  have tower := tower_of_rationals p n hp
  rcases tower with ⟨ x, y, _, defy, _ ⟩
  use y
  constructor
  . unfold are_rational_root_two at hp
    rcases hp with ⟨ nnz, _ ⟩
    have ynz : 0 < y := by
      rw [<-defy] at nnz
      exact Nat.pos_of_mul_pos_right nnz
    rw [<-defy]
    have := Nat.mul_lt_mul_of_pos_left (by decide: 1<2) ynz
    rw [Nat.mul_one] at this
    assumption
  . unfold part_of_root_of_two
    use x

theorem no_rational_root_of_two (a b : ℕ): ¬ are_rational_root_two a b := by
  intro h
  have prb: part_of_root_of_two b := by
    unfold part_of_root_of_two
    use a
  have := tower_means_fail part_of_root_of_two part_implies_tower b prb
  contradiction
