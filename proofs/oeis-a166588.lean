import OMAStatements.S_oeis_a166588
import Mathlib

-- Problem: A166588, Mathar's conjectured recurrence for the partial sums of A097331.
-- Upstream: formal-conjectures statements/oeis-a166588.lean (declaration OMA.S_oeis_a166588.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof: since a(n) - a(n-1) = b(n), the recurrence reads (n+1) b(n) = 4 (n-2) b(n-2). For even
-- n >= 4 both sides vanish; for n = 2s+3 it is (2s+4) C(s+1) = 4 (2s+1) C(s), the Catalan
-- recurrence (from (n+1) C(n) = binom(2n, n) and the central binomial recurrence).

namespace OMA.P_oeis_a166588

open OMA.S_oeis_a166588

theorem cat_rec (s : ℕ) : (s + 2) * catalan (s + 1) = 2 * (2 * s + 1) * catalan s := by
  have h1 := succ_mul_catalan_eq_centralBinom (s + 1)
  have h2 := succ_mul_catalan_eq_centralBinom s
  have h3 := Nat.succ_mul_centralBinom_succ s
  have h : (s + 1) * ((s + 2) * catalan (s + 1)) = (s + 1) * (2 * (2 * s + 1) * catalan s) := by
    rw [show s + 2 = s + 1 + 1 from rfl, h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos s) h

theorem b_odd (s : ℕ) : b (2 * s + 1) = (catalan s : ℤ) := by
  unfold b
  rw [if_neg (by omega), if_pos (by omega), show (2 * s + 1 - 1) / 2 = s by omega]

theorem b_even (s : ℕ) : b (2 * s + 2) = 0 := by
  unfold b
  rw [if_neg (by omega), if_neg (by omega)]

theorem a_succ (m : ℕ) : a (m + 1) = a m + b (m + 1) := by
  unfold a
  rw [Finset.sum_range_succ]

theorem main' : ∀ n : ℕ, 3 ≤ n →
    (-(n : ℤ) - 1) * a n + ((n : ℤ) + 1) * a (n - 1) + 4 * ((n : ℤ) - 2) * a (n - 2)
      + 4 * (-(n : ℤ) + 2) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  have e3 : a (k + 3) = a (k + 2) + b (k + 3) := a_succ (k + 2)
  have e1 : a (k + 1) = a k + b (k + 1) := a_succ k
  have key : ((k : ℤ) + 4) * b (k + 3) = 4 * ((k : ℤ) + 1) * b (k + 1) := by
    rcases Nat.even_or_odd' k with ⟨s, rfl | rfl⟩
    · rw [show 2 * s + 3 = 2 * (s + 1) + 1 by ring, b_odd (s + 1), b_odd s]
      have hz : ((s : ℤ) + 2) * (catalan (s + 1) : ℤ) = 2 * (2 * (s : ℤ) + 1) * (catalan s : ℤ) := by
        exact_mod_cast cat_rec s
      push_cast
      linear_combination 2 * hz
    · rw [show 2 * s + 1 + 3 = 2 * (s + 1) + 2 by ring, show 2 * s + 1 + 1 = 2 * s + 2 by ring,
        b_even (s + 1), b_even s]
      ring
  push_cast
  linear_combination (-1 : ℤ) * key - ((k : ℤ) + 4) * e3 + 4 * ((k : ℤ) + 1) * e1

end OMA.P_oeis_a166588

theorem OMA.solution : type_of% @OMA.S_oeis_a166588.main := OMA.P_oeis_a166588.main'
