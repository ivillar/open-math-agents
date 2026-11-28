import OMAStatements.S_oeis_a124753
import Mathlib

-- Problem: A124753, Mathar's conjectured order-6 recurrence for
-- a(3m + r) = (r + 1) C(4m + r, m) / (3m + r + 1), r = 0, 1, 2.
-- Upstream: formal-conjectures statements/oeis-a124753.lean (declaration OMA.S_oeis_a124753.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof: on each residue class mod 3 the term is an explicit factorial quotient in m; splitting n by
-- its residue, the seven terms of the recurrence are rational multiples of the same factorials and the
-- recurrence reduces to an identity of rational functions.

namespace OMA.P_oeis_a124753

open OMA.S_oeis_a124753

theorem A0 (m : ℕ) : a (3 * m + 0) = (1 : ℚ) * (((4 * m + 0).factorial : ℚ)
    / ((m.factorial : ℚ) * ((3 * m + 0).factorial : ℚ))) / (3 * (m : ℚ) + 1) := by
  unfold a
  rw [show (3 * m + 0) % 3 = 0 by omega, show (3 * m + 0) / 3 = m by omega,
    show 4 * m + 0 = 4 * m + 0 from rfl]
  rw [Nat.cast_choose ℚ (show m ≤ 4 * m + 0 by omega), show 4 * m + 0 - m = 3 * m + 0 by omega]
  push_cast
  ring

theorem A1 (m : ℕ) : a (3 * m + 1) = (2 : ℚ) * (((4 * m + 1).factorial : ℚ)
    / ((m.factorial : ℚ) * ((3 * m + 1).factorial : ℚ))) / (3 * (m : ℚ) + 2) := by
  unfold a
  rw [show (3 * m + 1) % 3 = 1 by omega, show (3 * m + 1) / 3 = m by omega,
    show 4 * m + 1 = 4 * m + 1 from rfl]
  rw [Nat.cast_choose ℚ (show m ≤ 4 * m + 1 by omega), show 4 * m + 1 - m = 3 * m + 1 by omega]
  push_cast
  ring

theorem A2 (m : ℕ) : a (3 * m + 2) = (3 : ℚ) * (((4 * m + 2).factorial : ℚ)
    / ((m.factorial : ℚ) * ((3 * m + 2).factorial : ℚ))) / (3 * (m : ℚ) + 3) := by
  unfold a
  rw [show (3 * m + 2) % 3 = 2 by omega, show (3 * m + 2) / 3 = m by omega,
    show 4 * m + 2 = 4 * m + 2 from rfl]
  rw [Nat.cast_choose ℚ (show m ≤ 4 * m + 2 by omega), show 4 * m + 2 - m = 3 * m + 2 by omega]
  push_cast
  ring

theorem main' : ∀ n : ℕ, 6 ≤ n →
    8019 * (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) + 1) * a n
      + 17496 * (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 3) * a (n - 1)
      + 2592 * (3 * (n : ℚ) - 5) * ((n : ℚ) - 1) * (3 * (n : ℚ) - 16) * a (n - 2)
      + 216 * (-224 * (n : ℚ) ^ 3 + 48 * (n : ℚ) ^ 2 + 3926 * (n : ℚ) - 6331) * a (n - 3)
      + 576 * (-288 * (n : ℚ) ^ 3 + 2448 * (n : ℚ) ^ 2 - 6558 * (n : ℚ) + 5443) * a (n - 4)
      + 768 * (-288 * (n : ℚ) ^ 3 + 3600 * (n : ℚ) ^ 2 - 14878 * (n : ℚ) + 20375) * a (n - 5)
      - 8192 * (4 * (n : ℚ) - 23) * (2 * (n : ℚ) - 11) * (4 * (n : ℚ) - 21) * a (n - 6) = 0 := by
  intro n hn
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 3 ∧ n = 3 * m + r := ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  interval_cases r
  · rw [show 3 * (j + 2) + 0 = 3 * (j + 2) + 0 from rfl, show 3 * (j + 2) + 0 - 1 = 3 * (j + 1) + 2 by omega, show 3 * (j + 2) + 0 - 2 = 3 * (j + 1) + 1 by omega, show 3 * (j + 2) + 0 - 3 = 3 * (j + 1) + 0 by omega, show 3 * (j + 2) + 0 - 4 = 3 * (j + 0) + 2 by omega, show 3 * (j + 2) + 0 - 5 = 3 * (j + 0) + 1 by omega, show 3 * (j + 2) + 0 - 6 = 3 * (j + 0) + 0 by omega]
    rw [A0 (j + 2), A2 (j + 1), A1 (j + 1), A0 (j + 1), A2 (j + 0), A1 (j + 0), A0 (j + 0)]
    simp only [Nat.mul_add, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.mul_zero]
    have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((3 * j).factorial : ℚ) ≠ 0 := by positivity
    have h4 : ((4 * j).factorial : ℚ) ≠ 0 := by positivity
    have p : (0 : ℚ) ≤ j := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · rw [show 3 * (j + 2) + 1 = 3 * (j + 2) + 1 from rfl, show 3 * (j + 2) + 1 - 1 = 3 * (j + 2) + 0 by omega, show 3 * (j + 2) + 1 - 2 = 3 * (j + 1) + 2 by omega, show 3 * (j + 2) + 1 - 3 = 3 * (j + 1) + 1 by omega, show 3 * (j + 2) + 1 - 4 = 3 * (j + 1) + 0 by omega, show 3 * (j + 2) + 1 - 5 = 3 * (j + 0) + 2 by omega, show 3 * (j + 2) + 1 - 6 = 3 * (j + 0) + 1 by omega]
    rw [A1 (j + 2), A0 (j + 2), A2 (j + 1), A1 (j + 1), A0 (j + 1), A2 (j + 0), A1 (j + 0)]
    simp only [Nat.mul_add, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.mul_zero]
    have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((3 * j).factorial : ℚ) ≠ 0 := by positivity
    have h4 : ((4 * j).factorial : ℚ) ≠ 0 := by positivity
    have p : (0 : ℚ) ≤ j := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · rw [show 3 * (j + 2) + 2 = 3 * (j + 2) + 2 from rfl, show 3 * (j + 2) + 2 - 1 = 3 * (j + 2) + 1 by omega, show 3 * (j + 2) + 2 - 2 = 3 * (j + 2) + 0 by omega, show 3 * (j + 2) + 2 - 3 = 3 * (j + 1) + 2 by omega, show 3 * (j + 2) + 2 - 4 = 3 * (j + 1) + 1 by omega, show 3 * (j + 2) + 2 - 5 = 3 * (j + 1) + 0 by omega, show 3 * (j + 2) + 2 - 6 = 3 * (j + 0) + 2 by omega]
    rw [A2 (j + 2), A1 (j + 2), A0 (j + 2), A2 (j + 1), A1 (j + 1), A0 (j + 1), A2 (j + 0)]
    simp only [Nat.mul_add, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.mul_zero]
    have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((3 * j).factorial : ℚ) ≠ 0 := by positivity
    have h4 : ((4 * j).factorial : ℚ) ≠ 0 := by positivity
    have p : (0 : ℚ) ≤ j := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring

end OMA.P_oeis_a124753

theorem OMA.solution : type_of% @OMA.S_oeis_a124753.main := OMA.P_oeis_a124753.main'
