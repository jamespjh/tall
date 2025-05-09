-- Proofs from chapter 2 of "Foundations of Mathametics by Stewart and Tall".
def m : Nat := 1
#print m
#check Nat.succ_ne_zero

theorem m_eq : m = 1 := by
  rfl

-- Root 2 is irrational

-- theorem root_2_irrational : ¬∃ (p q : ℤ), q ≠ 0 ∧ (p / q) ^ 2 = 2 := by
