import OMAStatements.S_oeis_a081181
import Mathlib

-- Problem: A081181, the conjectured P-recurrence for a(n) = C(floor((n+1)/2) + n + 1, n).
-- Upstream: formal-conjectures statements/oeis-a081181.lean (declaration OMA.S_oeis_a081181.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof: on even and odd n the term is an explicit binomial in m = floor(n/2), hence a factorial
-- quotient; splitting n by parity, all terms of the recurrence are rational multiples of the same
-- factorials and the recurrence reduces to an identity of rational functions.

namespace OMA.P_oeis_a081181

open OMA.S_oeis_a081181

theorem A_even (m : ℕ) : (a (2 * m) : ℚ) = ((3 * m + 1).factorial : ℚ) / (((2 * m).factorial : ℚ) * ((m + 1).factorial : ℚ)) := by
  unfold a
  rw [show (2 * m + 1) / 2 + (2 * m + 1) = 3 * m + 1 by omega, Nat.cast_choose ℚ (show 2 * m ≤ 3 * m + 1 by omega),
    show 3 * m + 1 - (2 * m) = m + 1 by omega]

theorem A_odd (m : ℕ) : (a (2 * m + 1) : ℚ) = ((3 * m + 3).factorial : ℚ) / (((2 * m + 1).factorial : ℚ) * ((m + 2).factorial : ℚ)) := by
  unfold a
  rw [show (2 * m + 1 + 1) / 2 + (2 * m + 1 + 1) = 3 * m + 3 by omega, Nat.cast_choose ℚ (show 2 * m + 1 ≤ 3 * m + 3 by omega),
    show 3 * m + 3 - (2 * m + 1) = m + 2 by omega]

theorem main' : ∀ n : ℕ, 3 ≤ n →
      8 * (n : ℤ) * (n + 3) * (1845 * n - 2882) * a n
        + 4 * (-5097 * (n : ℤ) ^ 3 + 11143 * n ^ 2 + 42110 * n - 27416) * a (n - 1)
        + 6 * (-16605 * (n : ℤ) ^ 3 - 7272 * n ^ 2 - 16701 * n + 9490) * a (n - 2)
        + 3 * (3 * (n : ℤ) - 5) * (5097 * n - 949) * (3 * n - 4) * a (n - 3) = 0 := by
  intro n hn
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

end OMA.P_oeis_a081181

theorem OMA.solution : type_of% @OMA.S_oeis_a081181.main := OMA.P_oeis_a081181.main'
