import OMAStatements.S_oeis_a348618
import Mathlib

-- Problem: A348618, Mathar's conjectured recurrence n (n-1) a(n) = 12 (3n-2)(3n-4) a(n-2).
-- Upstream: formal-conjectures statements/oeis-a348618.lean (declaration OMA.S_oeis_a348618.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof: the recurrence only relates terms of the same parity. For even n = 2k+2 the term is
-- 16^(k+1) C(3k+2, 2k+2), and for odd n = 2m+1 it is C(3m+1, 2m+1) C(6m+2, 3m+1) / C(2m, m); in both cases
-- the ratio a(n)/a(n-2) is an explicit rational function and the recurrence is an identity.

namespace OMA.P_oeis_a348618

open OMA.S_oeis_a348618

theorem A_even (k : ℕ) : a (2 * (k + 1)) = (16 : ℚ) ^ (k + 1) * (((3 * k + 2).factorial : ℚ)
    / (((2 * k + 2).factorial : ℚ) * (k.factorial : ℚ))) := by
  unfold a
  have hp : ((-1 : ℚ)) ^ (2 * (k + 1)) = 1 := by rw [pow_mul]; norm_num
  rw [hp, show 3 * (2 * (k + 1)) / 2 - 1 = 3 * k + 2 by omega,
    Nat.cast_choose ℚ (show 2 * (k + 1) ≤ 3 * k + 2 by omega), show 3 * k + 2 - 2 * (k + 1) = k by omega,
    show 2 * (k + 1) = 2 * k + 2 by ring, show (4 : ℚ) ^ (2 * k + 2) = 16 ^ (k + 1) by
      rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]; norm_num]
  ring

theorem A_odd (m : ℕ) : a (2 * m + 1) = ((3 * m + 1).factorial : ℚ) / (((2 * m + 1).factorial : ℚ) * (m.factorial : ℚ))
    * (((6 * m + 2).factorial : ℚ) / (((3 * m + 1).factorial : ℚ) * ((3 * m + 1).factorial : ℚ)))
    / (((2 * m).factorial : ℚ) / ((m.factorial : ℚ) * (m.factorial : ℚ))) := by
  unfold a
  have hp : ((-1 : ℚ)) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [hp, show (3 * (2 * m + 1) - 1) / 2 = 3 * m + 1 by omega, show 3 * (2 * m + 1) - 1 = 6 * m + 2 by omega,
    show 2 * m + 1 - 1 = 2 * m by omega, show 2 * m / 2 = m by omega]
  push_cast
  rw [Nat.cast_choose ℚ (show 2 * m + 1 ≤ 3 * m + 1 by omega), Nat.cast_choose ℚ (show 3 * m + 1 ≤ 6 * m + 2 by omega),
    Nat.cast_choose ℚ (show m ≤ 2 * m by omega), show 3 * m + 1 - (2 * m + 1) = m by omega,
    show 6 * m + 2 - (3 * m + 1) = 3 * m + 1 by omega, show 2 * m - m = m by omega]
  ring

theorem main' : ∀ n : ℕ, 3 ≤ n →
      (n : ℚ) * ((n : ℚ) - 1) * a n -
        12 * (3 * (n : ℚ) - 2) * (3 * (n : ℚ) - 4) * a (n - 2) = 0 := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    rw [show 2 * (k + 2) - 2 = 2 * (k + 1) by omega, show 2 * (k + 2) = 2 * ((k + 1) + 1) by ring]
    rw [A_even (k + 1), A_even k]
    rw [show 3 * (k + 1) + 2 = 3 * k + 5 by ring, show 2 * (k + 1) + 2 = 2 * k + 4 by ring]
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((3 * k).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (k + 1) + 1 - 2 = 2 * k + 1 by omega]
    rw [A_odd (k + 1), A_odd k]
    rw [show 3 * (k + 1) + 1 = 3 * k + 4 by ring, show 2 * (k + 1) + 1 = 2 * k + 3 by ring,
      show 6 * (k + 1) + 2 = 6 * k + 8 by ring, show 2 * (k + 1) = 2 * k + 2 by ring]
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((3 * k).factorial : ℚ) ≠ 0 := by positivity
    have h4 : ((6 * k).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring

end OMA.P_oeis_a348618

theorem OMA.solution : type_of% @OMA.S_oeis_a348618.main := OMA.P_oeis_a348618.main'
