import OMAStatements.S_oeis_a192755
import Mathlib

/-!
Credit: @ivillar
Proof: let g = x^2 - x - 1 and c(m) = 5m + 1. If p(n) mod g = v x + u, then
x p(n) + c(n+1) is congruent to (u + v) x + (v + c(n+1)), so the remainders satisfy
v(n+1) = u(n) + v(n), u(n+1) = v(n) + c(n+1), with u(0) = 1, v(0) = 0, and a(n) = v(n).
Then v(k+2) = v(k+1) + v(k) + c(k+1), and since c is linear,
v(m+4) - 3 v(m+3) + 2 v(m+2) + v(m+1) - v(m) = 0. The denominator of the g.f. is
(x^2+x-1)(x-1)^2 = x^4 - x^3 - 2x^2 + 3x - 1, and the first four terms give -x - 4x^2.
-/

namespace OMAA192755Helpers
open Polynomial OMA.S_oeis_a192755

/-- The remainder pair (u(n), v(n)) of p(n) modulo x^2 - x - 1. -/
def UV : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((UV n).2 + (5 * ((n : ℤ) + 1) + 1), (UV n).1 + (UV n).2)

def U (n : ℕ) : ℤ := (UV n).1

def V (n : ℕ) : ℤ := (UV n).2

theorem hg : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!

theorem hdeg : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by compute_degree!

theorem lin_rem (u v : ℤ) : (C v * X + C u) %ₘ (X ^ 2 - X - 1 : ℤ[X]) = C v * X + C u :=
  (modByMonic_eq_self_iff hg).mpr (lt_of_le_of_lt degree_linear_le (by rw [hdeg]; decide))

theorem R_eq (n : ℕ) : p n %ₘ (X ^ 2 - X - 1 : ℤ[X]) = C (V n) * X + C (U n) := by
  induction n with
  | zero =>
    show (1 : ℤ[X]) %ₘ (X ^ 2 - X - 1 : ℤ[X]) = C (V 0) * X + C (U 0)
    rw [(modByMonic_eq_self_iff (p := (1 : ℤ[X])) hg).mpr (by rw [hdeg, degree_one]; decide)]
    simp [U, V, UV]
  | succ n ih =>
    have h := modByMonic_add_div (p n) (X ^ 2 - X - 1 : ℤ[X])
    rw [ih] at h
    have hdiv : (X ^ 2 - X - 1 : ℤ[X]) ∣
        p (n + 1) - (C (V (n + 1)) * X + C (U (n + 1))) := by
      refine ⟨X * (p n /ₘ (X ^ 2 - X - 1)) + C (V n), ?_⟩
      show X * p n + C (5 * ((n : ℤ) + 1) + 1) -
          (C (U n + V n) * X + C (V n + (5 * ((n : ℤ) + 1) + 1))) = _
      simp only [C_add]
      linear_combination (-X) * h
    rw [modByMonic_eq_of_dvd_sub hg hdiv, lin_rem]

theorem a_eq_V (n : ℕ) : a n = V n := by
  unfold a
  rw [R_eq, coeff_add, coeff_C_mul_X, coeff_C]
  simp

theorem w (k : ℕ) : V (k + 2) = V (k + 1) + V k + (5 * ((k : ℤ) + 1) + 1) := by
  show (V k + (5 * ((k : ℤ) + 1) + 1)) + V (k + 1) = _
  ring

theorem Vrec (m : ℕ) : V (m + 4) - 3 * V (m + 3) + 2 * V (m + 2) + V (m + 1) - V m = 0 := by
  have h2 : V (m + 4) = V (m + 3) + V (m + 2) + (5 * ((m : ℤ) + 3) + 1) := by
    have := w (m + 2); push_cast at this; linarith
  have h1 : V (m + 3) = V (m + 2) + V (m + 1) + (5 * ((m : ℤ) + 2) + 1) := by
    have := w (m + 1); push_cast at this; linarith
  have h0 : V (m + 2) = V (m + 1) + V m + (5 * ((m : ℤ) + 1) + 1) := w m
  linarith

end OMAA192755Helpers

namespace OMAA192755PS
open PowerSeries

theorem coeff_mk_mul_X_pow (f : ℕ → ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (f : ℕ → ℤ) (r : ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * (if k ≤ n then f (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (f : ℕ → ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * X ^ k) = f j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem coeff_at_C (f : ℕ → ℤ) (r : ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * f j := by
  rw [mul_left_comm, coeff_C_mul, coeff_at f n k j h]

end OMAA192755PS

open PowerSeries OMAA192755Helpers OMAA192755PS in
theorem OMA.solution : type_of% @OMA.S_oeis_a192755.main := by
  have hfun : OMA.S_oeis_a192755.a = V := funext a_eq_V
  rw [hfun]
  ext n
  have hD : ((X ^ 2 + X - 1) * (X - 1) ^ 2 : PowerSeries ℤ) =
      X ^ 4 - X ^ 3 - C 2 * X ^ 2 + C 3 * X ^ 1 - X ^ 0 := by
    rw [map_ofNat C 2, map_ofNat C 3]; ring
  have hN : (-(X : PowerSeries ℤ) * (1 + 4 * X)) = -X ^ 1 - C 4 * X ^ 2 := by
    rw [map_ofNat C 4]; ring
  rw [hD, hN]
  have v0 : V 0 = 0 := by decide
  have v1 : V 1 = 1 := by decide
  have v2 : V 2 = 7 := by decide
  have v3 : V 3 = 19 := by decide
  rcases Nat.lt_or_ge n 4 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, map_neg, coeff_mk_mul_C_X_pow,
      coeff_mk_mul_X_pow, coeff_C_mul, coeff_X_pow]
    interval_cases n
    · norm_num [v0]
    · norm_num [v0, v1]
    · norm_num [v0, v1, v2]
    · norm_num [v0, v1, v2, v3]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub, map_neg]
    rw [coeff_at V (m + 4) 4 m (by omega), coeff_at V (m + 4) 3 (m + 1) (by omega),
      coeff_at_C V 2 (m + 4) 2 (m + 2) (by omega), coeff_at_C V 3 (m + 4) 1 (m + 3) (by omega),
      coeff_at V (m + 4) 0 (m + 4) (by omega), coeff_C_mul, coeff_X_pow, coeff_X_pow,
      if_neg (by omega), if_neg (by omega)]
    linear_combination -(Vrec m)
