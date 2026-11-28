import OMAStatements.S_oeis_a081204
import Mathlib

-- Problem: A081204, the two conjectured P-recurrences for a(n) = C(floor((n+1)/2) + n, n).
-- Upstream: formal-conjectures statements/oeis-a081204.lean (declaration OMA.S_oeis_a081204.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof: on even and odd n the term is an explicit binomial in m = floor(n/2), hence a factorial
-- quotient; splitting n by parity, all terms of the recurrence are rational multiples of the same
-- factorials and the recurrence reduces to an identity of rational functions.

namespace OMA.P_oeis_a081204

open OMA.S_oeis_a081204

theorem A_even (m : ℕ) : (a (2 * m) : ℚ) = ((3 * m).factorial : ℚ) / (((2 * m).factorial : ℚ) * ((m).factorial : ℚ)) := by
  unfold a
  rw [show (2 * m + 1) / 2 + 2 * m = 3 * m by omega, Nat.cast_choose ℚ (show 2 * m ≤ 3 * m by omega),
    show 3 * m - (2 * m) = m by omega]

theorem A_odd (m : ℕ) : (a (2 * m + 1) : ℚ) = ((3 * m + 2).factorial : ℚ) / (((2 * m + 1).factorial : ℚ) * ((m + 1).factorial : ℚ)) := by
  unfold a
  rw [show (2 * m + 1 + 1) / 2 + (2 * m + 1) = 3 * m + 2 by omega, Nat.cast_choose ℚ (show 2 * m + 1 ≤ 3 * m + 2 by omega),
    show 3 * m + 2 - (2 * m + 1) = m + 1 by omega]

theorem main' : (∀ n : ℕ, 2 ≤ n →
      4 * (n : ℤ) * (n + 1) * (6 * n ^ 2 - 15 * n + 8) * a n + 6 * (n : ℤ) * (9 * n - 7) * a (n - 1)
        - 3 * (3 * (n : ℤ) - 4) * (3 * n - 2) * (6 * n ^ 2 - 3 * n - 1) * a (n - 2) = 0) ∧
    (∀ n : ℕ, 3 ≤ n →
      8 * (n : ℤ) ^ 2 * (n + 1) * a n - 12 * (n : ℤ) * (83 * n ^ 2 - 313 * n + 232) * a (n - 1)
        + 6 * (-9 * (n : ℤ) ^ 3 - 377 * n + 384) * a (n - 2)
        + 9 * (3 * (n : ℤ) - 5) * (83 * n - 64) * (3 * n - 7) * a (n - 3) = 0) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    apply Int.cast_injective (α := ℚ)
    push_cast
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rw [show 2 * (j + 1) - 1 = 2 * (j + 0) + 1 by omega, show 2 * (j + 1) - 2 = 2 * (j + 0) by omega]
      rw [A_even (j + 1), A_odd (j + 0), A_even (j + 0)]
      simp only [Nat.mul_add, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.mul_zero]
      have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
      have h2 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
      have h3 : ((3 * j).factorial : ℚ) ≠ 0 := by positivity
      simp only [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rw [show 2 * (j + 1) + 1 - 1 = 2 * (j + 1) by omega, show 2 * (j + 1) + 1 - 2 = 2 * (j + 0) + 1 by omega]
      rw [A_odd (j + 1), A_even (j + 1), A_odd (j + 0)]
      simp only [Nat.mul_add, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.mul_zero]
      have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
      have h2 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
      have h3 : ((3 * j).factorial : ℚ) ≠ 0 := by positivity
      simp only [Nat.factorial_succ]
      push_cast
      field_simp
      ring
  · intro n hn
    apply Int.cast_injective (α := ℚ)
    push_cast
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
      rw [show 2 * (j + 2) - 1 = 2 * (j + 1) + 1 by omega, show 2 * (j + 2) - 2 = 2 * (j + 1) by omega, show 2 * (j + 2) - 3 = 2 * (j + 0) + 1 by omega]
      rw [A_even (j + 2), A_odd (j + 1), A_even (j + 1), A_odd (j + 0)]
      simp only [Nat.mul_add, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.mul_zero]
      have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
      have h2 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
      have h3 : ((3 * j).factorial : ℚ) ≠ 0 := by positivity
      simp only [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rw [show 2 * (j + 1) + 1 - 1 = 2 * (j + 1) by omega, show 2 * (j + 1) + 1 - 2 = 2 * (j + 0) + 1 by omega, show 2 * (j + 1) + 1 - 3 = 2 * (j + 0) by omega]
      rw [A_odd (j + 1), A_even (j + 1), A_odd (j + 0), A_even (j + 0)]
      simp only [Nat.mul_add, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.mul_zero]
      have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
      have h2 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
      have h3 : ((3 * j).factorial : ℚ) ≠ 0 := by positivity
      simp only [Nat.factorial_succ]
      push_cast
      field_simp
      ring

end OMA.P_oeis_a081204

theorem OMA.solution : type_of% @OMA.S_oeis_a081204.main := OMA.P_oeis_a081204.main'
