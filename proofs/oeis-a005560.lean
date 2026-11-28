import OMAStatements.S_oeis_a005560
import Mathlib

-- Problem: A005560, Mathar's conjectured recurrence for column 2 of A052174 (walks on the square lattice),
-- given by a binomial formula with floors.
-- Upstream: formal-conjectures statements/oeis-a005560.lean (declaration OMA.S_oeis_a005560.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof: on each parity class of u = n - 3 every binomial is an explicit factorial quotient in k;
-- splitting by parity, the three terms of the recurrence become rational multiples of the same
-- factorials and the recurrence reduces to an identity of rational functions (the first case is
-- checked directly).

namespace OMA.P_oeis_a005560

open OMA.S_oeis_a005560

theorem A_even (k : ℕ) : a (2 * k + 3) = ((2 * k + 4).factorial : ℚ) / (((k + 1).factorial : ℚ) * ((k + 3).factorial : ℚ)) * (((2 * k + 3).factorial : ℚ) / (((k).factorial : ℚ) * ((k + 3).factorial : ℚ))) - ((2 * k + 4).factorial : ℚ) / (((k).factorial : ℚ) * ((k + 4).factorial : ℚ)) * (((2 * k + 3).factorial : ℚ) / (((k).factorial : ℚ) * ((k + 3).factorial : ℚ))) := by
  rw [show 2 * k + 3 = 2 * k + 1 + 2 from by ring, a, column]
  simp only [show (2 * k + 2) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega,
    show 2 * k / 2 = k by omega]
  rw [show 2 + 2 * k + 1 + 1 = 2 * k + 4 by ring, show 2 + 2 * k + 1 = 2 * k + 3 by ring]
  rw [Nat.cast_choose ℚ (show k + 1 ≤ 2 * k + 4 by omega), Nat.cast_choose ℚ (show k ≤ 2 * k + 3 by omega),
    Nat.cast_choose ℚ (show k ≤ 2 * k + 4 by omega)]
  rw [show 2 * k + 4 - (k + 1) = k + 3 by omega, show 2 * k + 3 - k = k + 3 by omega,
    show 2 * k + 4 - k = k + 4 by omega]

theorem A_odd (k : ℕ) : a (2 * k + 4) = ((2 * k + 5).factorial : ℚ) / (((k + 1).factorial : ℚ) * ((k + 4).factorial : ℚ)) * (((2 * k + 4).factorial : ℚ) / (((k + 1).factorial : ℚ) * ((k + 3).factorial : ℚ))) - ((2 * k + 5).factorial : ℚ) / (((k + 1).factorial : ℚ) * ((k + 4).factorial : ℚ)) * (((2 * k + 4).factorial : ℚ) / (((k).factorial : ℚ) * ((k + 4).factorial : ℚ))) := by
  rw [show 2 * k + 4 = 2 * k + 1 + 1 + 2 from by ring, a, column]
  simp only [show (2 * k + 1 + 2) / 2 = k + 1 by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega,
    show (2 * k + 1) / 2 = k by omega]
  rw [show 2 + (2 * k + 1) + 1 + 1 = 2 * k + 5 by ring, show 2 + (2 * k + 1) + 1 = 2 * k + 4 by ring]
  rw [Nat.cast_choose ℚ (show k + 1 ≤ 2 * k + 5 by omega), Nat.cast_choose ℚ (show k + 1 ≤ 2 * k + 4 by omega),
    Nat.cast_choose ℚ (show k ≤ 2 * k + 4 by omega)]
  rw [show 2 * k + 5 - (k + 1) = k + 4 by omega, show 2 * k + 4 - (k + 1) = k + 3 by omega,
    show 2 * k + 4 - k = k + 4 by omega]

theorem main' : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) - 1) * (n - 2) * (2 * n + 1) * (n + 5) * (n + 4) * a n -
    4 * n * (n + 1) * (2 * (n : ℚ) ^ 2 + 4 * n + 19) * a (n - 1) -
    16 * (n : ℚ) ^ 2 * (n - 1) * (2 * n + 3) * (n + 1) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨u, rfl⟩ : ∃ u, n = u + 3 := ⟨n - 3, by omega⟩
  rcases Nat.even_or_odd' u with ⟨m, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      omega
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (k + 1) + 3 - 1 = 2 * k + 4 by omega, show 2 * (k + 1) + 3 - 2 = 2 * k + 3 by omega,
      show 2 * (k + 1) + 3 = 2 * (k + 1) + 3 from rfl]
    rw [A_even (k + 1), A_odd k, A_even k]
    rw [show 2 * (k + 1) + 4 = 2 * k + 6 by ring, show 2 * (k + 1) + 3 = 2 * k + 5 by ring]
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      norm_num [a, column, Nat.choose]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (k + 1) + 1 + 3 - 1 = 2 * (k + 1) + 3 by omega,
      show 2 * (k + 1) + 1 + 3 - 2 = 2 * k + 4 by omega,
      show 2 * (k + 1) + 1 + 3 = 2 * (k + 1) + 4 by ring]
    rw [A_odd (k + 1), A_even (k + 1), A_odd k]
    rw [show 2 * (k + 1) + 5 = 2 * k + 7 by ring, show 2 * (k + 1) + 4 = 2 * k + 6 by ring,
      show 2 * (k + 1) + 3 = 2 * k + 5 by ring]
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring

end OMA.P_oeis_a005560

theorem OMA.solution : type_of% @OMA.S_oeis_a005560.main := OMA.P_oeis_a005560.main'
