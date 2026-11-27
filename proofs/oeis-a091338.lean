import OMAStatements.S_oeis_a091338
import Mathlib

-- Problem: A091338, a(n) = (3/n) (Kronecker symbol); A.H.M. Smeets' conjectures.
-- Upstream: formal-conjectures statements/oeis-a091338.lean (declaration OMA.S_oeis_a091338.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Disproof: the last clause, a(24n+16) = -a(12n+4), recorded in the OEIS entry, fails at n = 0:
-- a(16) = (3/2)^4 (3/1) = 1 and a(4) = (3/2)^2 (3/1) = 1, so a(16) = 1 differs from -a(4) = -1.

namespace OMA.P_oeis_a091338

open OMA.S_oeis_a091338

theorem k1 : kronecker 3 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, kronecker]
  simp

theorem kron2_3 : kron2 3 = -1 := by
  unfold kron2
  norm_num

theorem k_two_mul (m : ℕ) (hm : 0 < m) : kronecker 3 (2 * m) = -kronecker 3 m := by
  obtain ⟨j, hj⟩ : ∃ j, 2 * m = j + 1 := ⟨2 * m - 1, by omega⟩
  rw [hj, kronecker, if_pos (by omega), kron2_3, show (j + 1) / 2 = m by omega]
  ring

theorem a4 : a 4 = 1 := by
  unfold a
  rw [show (4 : ℕ) = 2 * 2 by rfl, k_two_mul 2 (by norm_num), show (2 : ℕ) = 2 * 1 by rfl,
    k_two_mul 1 (by norm_num), k1]
  norm_num

theorem a16 : a 16 = 1 := by
  unfold a
  rw [show (16 : ℕ) = 2 * 8 by rfl, k_two_mul 8 (by norm_num), show (8 : ℕ) = 2 * 4 by rfl,
    k_two_mul 4 (by norm_num)]
  have h4 : kronecker 3 4 = 1 := a4
  rw [h4]
  norm_num

theorem disproof_main : ¬ ((∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n % 3 = 0)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (n % 12 = 1 ∨ n % 12 = 11 ∨ n % 48 = 4 ∨ n % 48 = 44) → a n = 1) ∧
    (∀ n : ℕ, 1 ≤ n →
      (n % 12 = 5 ∨ n % 12 = 7 ∨ n % 48 = 20 ∨ n % 48 = 28) → a n = -1) ∧
    a 2 = -1 ∧
    (∀ n : ℕ, a (12 * n + 10) = -a (12 * n + 2)) ∧
    (∀ n : ℕ, a (12 * n + 14) = a (12 * n + 10)) ∧
    (∀ n : ℕ, a (24 * n + 8) = -a (12 * n + 4)) ∧
    (∀ n : ℕ, a (24 * n + 16) = -a (12 * n + 4))) := by
  intro h
  have h8 := h.2.2.2.2.2.2.2 0
  simp only [Nat.mul_zero, Nat.zero_add] at h8
  rw [a16, a4] at h8
  norm_num at h8

end OMA.P_oeis_a091338

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a091338.main) :=
  OMA.P_oeis_a091338.disproof_main
