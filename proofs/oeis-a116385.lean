import OMAStatements.S_oeis_a116385
import Mathlib

-- Problem: A116385, Mathar's conjectured recurrence
-- (n+4) a(n) - 2 a(n-1) - (7n+8) a(n-2) + 6 a(n-3) + 12 (n-2) a(n-4) = 0.
-- Upstream: formal-conjectures statements/oeis-a116385.lean (declaration OMA.S_oeis_a116385.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof: for even n = 2j+4, a(n) = n! (1/((j+1)!(j+3)!) + 1/(j!(j+4)!)), and for odd n = 2j+3,
-- a(n) = 2 n!/(j!(j+3)!). For n >= 8 all five terms are covered by these closed forms and the
-- recurrence reduces to an identity of rational functions; n = 4..7 are checked directly.

namespace OMA.P_oeis_a116385

open OMA.S_oeis_a116385

theorem A_even (j : ℕ) : a (2 * (j + 2)) = ((2 * j + 4).factorial : ℚ) *
    (1 / (((j + 1).factorial : ℚ) * ((j + 3).factorial : ℚ)) + 1 / ((j.factorial : ℚ) * ((j + 4).factorial : ℚ))) := by
  unfold a i2 i3 i4
  have he : Even (2 * (j + 2)) := even_two_mul _
  have ho : ¬ Odd (2 * (j + 2)) := Nat.not_odd_iff_even.mpr he
  rw [if_pos ⟨he, by omega⟩, if_neg (fun h => ho h.1), if_pos ⟨he, by omega⟩,
    show (2 * (j + 2) - 2) / 2 = j + 1 by omega, show (2 * (j + 2) + 2) / 2 = j + 3 by omega,
    show (2 * (j + 2) - 4) / 2 = j by omega, show (2 * (j + 2) + 4) / 2 = j + 4 by omega,
    show 2 * (j + 2) = 2 * j + 4 by ring]
  ring

theorem A_odd (j : ℕ) : a (2 * (j + 1) + 1) = ((2 * j + 3).factorial : ℚ) *
    (2 * (1 / ((j.factorial : ℚ) * ((j + 3).factorial : ℚ)))) := by
  unfold a i2 i3 i4
  have ho : Odd (2 * (j + 1) + 1) := odd_two_mul_add_one _
  have he : ¬ Even (2 * (j + 1) + 1) := Nat.not_even_iff_odd.mpr ho
  rw [if_neg (fun h => he h.1), if_pos ⟨ho, by omega⟩, if_neg (fun h => he h.1),
    show (2 * (j + 1) + 1 - 3) / 2 = j by omega, show (2 * (j + 1) + 1 + 3) / 2 = j + 3 by omega,
    show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
  ring

theorem main' : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 4) * a n - 2 * a (n - 1) + (-7 * (n : ℚ) - 8) * a (n - 2) + 6 * a (n - 3)
      + 12 * ((n : ℚ) - 2) * a (n - 4) = 0 := by
  intro n hn
  by_cases hlt : n < 8
  · interval_cases n <;> norm_num [a, i2, i3, i4, Nat.factorial, Nat.even_iff, Nat.odd_iff]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 4 := ⟨m - 4, by omega⟩
    rw [show 2 * (j + 4) - 1 = 2 * (j + 2 + 1) + 1 by omega, show 2 * (j + 4) - 2 = 2 * (j + 1 + 2) by omega,
      show 2 * (j + 4) - 3 = 2 * (j + 1 + 1) + 1 by omega, show 2 * (j + 4) - 4 = 2 * (j + 2) by omega,
      show 2 * (j + 4) = 2 * (j + 2 + 2) by ring]
    rw [A_even (j + 2), A_odd (j + 2), A_even (j + 1), A_odd (j + 1), A_even j]
    rw [show 2 * (j + 2) + 4 = 2 * j + 8 by ring, show 2 * (j + 2) + 3 = 2 * j + 7 by ring,
      show 2 * (j + 1) + 4 = 2 * j + 6 by ring, show 2 * (j + 1) + 3 = 2 * j + 5 by ring]
    have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 4 := ⟨m - 4, by omega⟩
    rw [show 2 * (j + 4) + 1 - 1 = 2 * (j + 2 + 2) by omega, show 2 * (j + 4) + 1 - 2 = 2 * (j + 2 + 1) + 1 by omega,
      show 2 * (j + 4) + 1 - 3 = 2 * (j + 1 + 2) by omega, show 2 * (j + 4) + 1 - 4 = 2 * (j + 1 + 1) + 1 by omega,
      show 2 * (j + 4) + 1 = 2 * (j + 3 + 1) + 1 by ring]
    rw [A_odd (j + 3), A_even (j + 2), A_odd (j + 2), A_even (j + 1), A_odd (j + 1)]
    rw [show 2 * (j + 3) + 3 = 2 * j + 9 by ring, show 2 * (j + 2) + 4 = 2 * j + 8 by ring,
      show 2 * (j + 2) + 3 = 2 * j + 7 by ring, show 2 * (j + 1) + 4 = 2 * j + 6 by ring,
      show 2 * (j + 1) + 3 = 2 * j + 5 by ring]
    have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring

end OMA.P_oeis_a116385

theorem OMA.solution : type_of% @OMA.S_oeis_a116385.main := OMA.P_oeis_a116385.main'
