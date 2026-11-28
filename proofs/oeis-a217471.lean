import OMAStatements.S_oeis_a217471
import Mathlib

/-!
Credit: @ivillar
Proof: by induction on n. With x = F(2n+1) and y = F(2n+2) we have F(2n+3) = x + y and
Cassini's identity y^2 - xy - x^2 = (-1)^(2n+1) = -1. Writing G(t) for the right-hand side
as a polynomial in t = F(2n+1), the step G(x+y) = G(x) + y^5 holds because
G(x+y) - G(x) - y^5 = Q(x,y) (y^2 - xy - x^2 + 1) with
Q = (25/44) y - (10/11) y^3 - (5/11) x y^2 - (5/11) x^2 y.
-/

namespace OMAA217471Helpers

theorem cass (m : ℕ) : (Nat.fib (m + 1) : ℚ) ^ 2 - Nat.fib (m + 1) * Nat.fib m -
    (Nat.fib m : ℚ) ^ 2 = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : (Nat.fib (m + 1 + 1) : ℚ) = Nat.fib m + Nat.fib (m + 1) := by
      have e : Nat.fib (m + 1 + 1) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
      exact_mod_cast e
    rw [h, pow_succ]
    linear_combination -ih

end OMAA217471Helpers

open OMAA217471Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a217471.main := by
  intro n
  induction n with
  | zero => simp [OMA.S_oeis_a217471.a]
  | succ n ih =>
    have hsum : (OMA.S_oeis_a217471.a (n + 1) : ℚ) =
        OMA.S_oeis_a217471.a n + (Nat.fib (2 * n + 2) : ℚ) ^ 5 := by
      unfold OMA.S_oeis_a217471.a
      rw [Finset.sum_range_succ, show 2 * (n + 1) = 2 * n + 2 by ring]
      push_cast
      ring
    rw [hsum, ih]
    have hc : (Nat.fib (2 * n + 2) : ℚ) ^ 2 - Nat.fib (2 * n + 2) * Nat.fib (2 * n + 1) -
        (Nat.fib (2 * n + 1) : ℚ) ^ 2 = (-1) ^ (2 * n + 1) := cass (2 * n + 1)
    have hneg : ((-1 : ℚ)) ^ (2 * n + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    rw [hneg] at hc
    have e : Nat.fib (2 * (n + 1) + 1) = Nat.fib (2 * n + 1) + Nat.fib (2 * n + 2) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, Nat.fib_add_two]
    rw [e]
    push_cast
    linear_combination (-1 : ℚ) * ((25 / 44 : ℚ) * (Nat.fib (2 * n + 2) : ℚ) -
      (10 / 11 : ℚ) * (Nat.fib (2 * n + 2) : ℚ) ^ 3 -
      (5 / 11 : ℚ) * (Nat.fib (2 * n + 1) : ℚ) * (Nat.fib (2 * n + 2) : ℚ) ^ 2 -
      (5 / 11 : ℚ) * (Nat.fib (2 * n + 1) : ℚ) ^ 2 * (Nat.fib (2 * n + 2) : ℚ)) * hc
