import OMAStatements.S_mo_206157
import Mathlib

-- Problem: mo-206157, for a prime p >= 13 none of (p^2 - 1) / 2^k, k = 1..4, is prime.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Write p = 2t + 1, so p^2 - 1 = 4 t (t + 1). For k = 1, 2 the quotient is 2t(t+1) or t(t+1).
-- For k = 3 and k = 4 split t modulo 2 or 4; in every case the (floor) quotient is an explicit
-- product of two factors greater than 1, for example ((8s+3)^2 - 1) / 16 = s (4s + 3).

namespace MO206157

theorem helper (N c A B r : ℕ) (hN : N = c * (A * B) + r + 1) (hc : 0 < c) (hr : r < c)
    (hA : A ≠ 1) (hB : B ≠ 1) : ¬ ((N - 1) / c).Prime := by
  have h : (N - 1) / c = A * B := by
    rw [hN]
    have e : c * (A * B) + r + 1 - 1 = r + c * (A * B) := by omega
    rw [e, Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt hr, zero_add]
  rw [h]
  exact Nat.not_prime_mul hA hB

end MO206157

theorem OMA.solution : type_of% @OMA.S_mo_206157.main := by
  intro p hp h13 k hk1 hk4
  obtain ⟨t, ht⟩ := hp.odd_of_ne_two (by omega)
  interval_cases k
  · subst ht
    exact MO206157.helper _ _ (2 * t) (t + 1) 0 (by ring) (by norm_num) (by norm_num)
      (by omega) (by omega)
  · subst ht
    exact MO206157.helper _ _ t (t + 1) 0 (by ring) (by norm_num) (by norm_num)
      (by omega) (by omega)
  · obtain ⟨s, hs | hs⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
    · subst hs
      subst ht
      exact MO206157.helper _ _ s (2 * s + 1) 0 (by ring) (by norm_num) (by norm_num)
        (by omega) (by omega)
    · subst hs
      subst ht
      exact MO206157.helper _ _ (2 * s + 1) (s + 1) 0 (by ring) (by norm_num) (by norm_num)
        (by omega) (by omega)
  · obtain ⟨s, hs | hs | hs | hs⟩ :
        ∃ s, t = 4 * s ∨ t = 4 * s + 1 ∨ t = 4 * s + 2 ∨ t = 4 * s + 3 := ⟨t / 4, by omega⟩
    · subst hs
      subst ht
      exact MO206157.helper _ _ s (4 * s + 1) 0 (by ring) (by norm_num) (by norm_num)
        (by omega) (by omega)
    · subst hs
      subst ht
      exact MO206157.helper _ _ s (4 * s + 3) 8 (by ring) (by norm_num) (by norm_num)
        (by omega) (by omega)
    · subst hs
      subst ht
      exact MO206157.helper _ _ (4 * s + 1) (s + 1) 8 (by ring) (by norm_num) (by norm_num)
        (by omega) (by omega)
    · subst hs
      subst ht
      exact MO206157.helper _ _ (4 * s + 3) (s + 1) 0 (by ring) (by norm_num) (by norm_num)
        (by omega) (by omega)
