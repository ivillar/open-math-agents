import OMAStatements.S_mo_230382
import Mathlib

-- Problem: mo-230382, is C(N-1, r) the maximum of C(m0, j) C(m1, r-j) over m0 + m1 = N,
-- m0, m1 >= 1, for large N?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For N = 5000 and r = 4999 the guess is C(4999, 4999) = 1, but m0 = 1, m1 = 4999, j = 1
-- gives C(1,1) C(4999, 4998) = 4999.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_230382.main) := by
  intro h
  have hub := (h 5000 4999 le_rfl (by norm_num) (by norm_num)).2
  have e1 : Nat.choose 4999 4998 = 4999 := Nat.choose_succ_self_right 4998
  have hmem : (4999 : ℕ) ∈ {x : ℕ | ∃ m₀ m₁ j : ℕ, 1 ≤ m₀ ∧ 1 ≤ m₁ ∧ m₀ + m₁ = 5000 ∧
      j ≤ 4999 ∧ x = m₀.choose j * m₁.choose (4999 - j)} := by
    refine ⟨1, 4999, 1, le_rfl, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [Nat.choose_self, show (4999 : ℕ) - 1 = 4998 by norm_num, e1]
  have h1 := hub hmem
  have e2 : (5000 - 1 : ℕ).choose 4999 = 1 := by
    rw [show (5000 : ℕ) - 1 = 4999 by norm_num, Nat.choose_self]
  rw [e2] at h1
  omega
