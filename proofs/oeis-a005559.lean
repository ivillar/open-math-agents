import OMAStatements.S_oeis_a005559
import Mathlib

-- Problem: A005559, Mathar's conjectured recurrence for Hanna's binomial formula
-- a(j+2) = C(j+3, floor((j+2)/2)) C(j+2, floor((j+1)/2)) - C(j+3, floor((j+1)/2)) C(j+2, floor(j/2)).
-- Upstream: formal-conjectures statements/oeis-a005559.lean (declaration OMA.S_oeis_a005559.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof: on each parity class every binomial is an explicit factorial quotient in k; splitting n by
-- parity, the three terms of the recurrence become rational multiples of the same factorials and the
-- recurrence reduces to an identity of rational functions (n = 3 is checked directly).

namespace OMA.P_oeis_a005559

open OMA.S_oeis_a005559

theorem A_even (k : ℕ) : a (2 * k + 2) =
    ((2 * k + 3).factorial : ℚ) / (((k + 1).factorial : ℚ) * ((k + 2).factorial : ℚ)) *
      (((2 * k + 2).factorial : ℚ) / ((k.factorial : ℚ) * ((k + 2).factorial : ℚ))) -
    ((2 * k + 3).factorial : ℚ) / ((k.factorial : ℚ) * ((k + 3).factorial : ℚ)) *
      (((2 * k + 2).factorial : ℚ) / ((k.factorial : ℚ) * ((k + 2).factorial : ℚ))) := by
  rw [a]
  rw [show (2 * k + 2) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega, show 2 * k / 2 = k by omega]
  rw [Nat.cast_choose ℚ (show k + 1 ≤ 2 * k + 3 by omega), Nat.cast_choose ℚ (show k ≤ 2 * k + 2 by omega),
    Nat.cast_choose ℚ (show k ≤ 2 * k + 3 by omega)]
  rw [show 2 * k + 3 - (k + 1) = k + 2 by omega, show 2 * k + 2 - k = k + 2 by omega,
    show 2 * k + 3 - k = k + 3 by omega]

theorem A_odd (k : ℕ) : a (2 * k + 3) =
    ((2 * k + 4).factorial : ℚ) / (((k + 1).factorial : ℚ) * ((k + 3).factorial : ℚ)) *
      (((2 * k + 3).factorial : ℚ) / (((k + 1).factorial : ℚ) * ((k + 2).factorial : ℚ))) -
    ((2 * k + 4).factorial : ℚ) / (((k + 1).factorial : ℚ) * ((k + 3).factorial : ℚ)) *
      (((2 * k + 3).factorial : ℚ) / ((k.factorial : ℚ) * ((k + 3).factorial : ℚ))) := by
  rw [show 2 * k + 3 = (2 * k + 1) + 2 from rfl, a]
  rw [show (2 * k + 1 + 2) / 2 = k + 1 by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega,
    show (2 * k + 1) / 2 = k by omega, show 2 * k + 1 + 3 = 2 * k + 4 by omega,
    show 2 * k + 1 + 2 = 2 * k + 3 by omega]
  rw [Nat.cast_choose ℚ (show k + 1 ≤ 2 * k + 4 by omega), Nat.cast_choose ℚ (show k + 1 ≤ 2 * k + 3 by omega),
    Nat.cast_choose ℚ (show k ≤ 2 * k + 3 by omega)]
  rw [show 2 * k + 4 - (k + 1) = k + 3 by omega, show 2 * k + 3 - (k + 1) = k + 2 by omega,
    show 2 * k + 3 - k = k + 3 by omega]

theorem main' : ∀ n : ℕ, 3 ≤ n →
    -((n : ℚ) - 1) * (2 * n + 1) * (n + 4) * (n + 3) * a n +
    4 * (n + 1) * (2 * (n : ℚ) ^ 2 + 4 * n + 9) * a (n - 1) +
    16 * n * ((n : ℚ) - 1) * (2 * n + 3) * (n + 1) * a (n - 2) = 0 := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨i, rfl⟩ : ∃ i, m = i + 2 := ⟨m - 2, by omega⟩
    rw [show 2 * (i + 2) - 1 = 2 * i + 3 by omega, show 2 * (i + 2) - 2 = 2 * i + 2 by omega,
      show 2 * (i + 2) = 2 * (i + 1) + 2 by ring]
    rw [A_even (i + 1), A_odd i, A_even i]
    rw [show 2 * (i + 1) + 3 = 2 * i + 5 by ring, show 2 * (i + 1) + 2 = 2 * i + 4 by ring]
    have h1 : (i.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * i).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      norm_num [a, Nat.choose]
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (i + 1) + 1 - 1 = 2 * i + 2 by omega, show 2 * (i + 1) + 1 - 2 = 2 * i + 1 by omega,
      show 2 * (i + 1) + 1 = 2 * i + 3 by ring]
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      norm_num [a, Nat.choose]
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [show 2 * (k + 1) + 3 = 2 * (k + 1) + 3 from rfl, show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
    rw [A_odd (k + 1), A_even (k + 1), A_odd k]
    rw [show 2 * (k + 1) + 4 = 2 * k + 6 by ring, show 2 * (k + 1) + 3 = 2 * k + 5 by ring,
      show 2 * (k + 1) + 2 = 2 * k + 4 by ring]
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring

end OMA.P_oeis_a005559

theorem OMA.solution : type_of% @OMA.S_oeis_a005559.main := OMA.P_oeis_a005559.main'
