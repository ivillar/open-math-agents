import OMAStatements.S_oeis_a192759
import Mathlib

/-!
Credit: @ivillar
Proof: let g = x^2 - x - 1 and c(m) = floor((m+5)/5). If p(n) mod g = v x + u, then
x p(n) + c(n+1) = x (g q + v x + u) + c(n+1) is congruent to (u + v) x + (v + c(n+1)), so the
remainders satisfy v(n+1) = u(n) + v(n), u(n+1) = v(n) + c(n+1), with u(0) = 1, v(0) = 0, and
a(n) = v(n). Then u(n+2) = u(n+1) + u(n) + [5 | n+2], so u(n) = A124502(n+1), and
v(n+1) = v(n) + u(n) gives the partial sums. Also v(k+2) = v(k+1) + v(k) + c(k+1) and
c(m+6) - c(m+5) - c(m+1) + c(m) = 0 give
v(m+8) - 2v(m+7) + v(m+5) - v(m+3) + 2v(m+2) - v(m) = 0; the denominator of the g.f. is
(x^2+x-1)(x^5-1)(x-1) = x^8 - 2x^6 + x^5 - x^3 + 2x - 1, and the first eight terms give the g.f.
-/

namespace OMAA192759Helpers
open Polynomial OMA.S_oeis_a192759

/-- The remainder pair (u(n), v(n)) of p(n) modulo x^2 - x - 1. -/
def UV : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((UV n).2 + ((((n + 1) + 5) / 5 : ℕ) : ℤ), (UV n).1 + (UV n).2)

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
      show X * p n + C ((((n + 1) + 5) / 5 : ℕ) : ℤ) -
          (C (U n + V n) * X + C (V n + ((((n + 1) + 5) / 5 : ℕ) : ℤ))) = _
      rw [C_add, C_add]
      linear_combination (-X) * h
    rw [modByMonic_eq_of_dvd_sub hg hdiv, lin_rem]

theorem a_eq_V (n : ℕ) : a n = V n := by
  unfold a
  rw [R_eq, coeff_add, coeff_C_mul_X, coeff_C]
  simp

theorem w (k : ℕ) : V (k + 2) = V (k + 1) + V k + (((k + 1 + 5) / 5 : ℕ) : ℤ) := by
  show (V k + (((k + 1 + 5) / 5 : ℕ) : ℤ)) + V (k + 1) = _
  ring

theorem UA (n : ℕ) : U n = A124502 (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · rfl
    · decide
    · have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have hv : V (n + 1) = U n + V n := rfl
      have hu1 : U (n + 1) = V n + (((n + 1 + 5) / 5 : ℕ) : ℤ) := rfl
      have hu2 : U (n + 1 + 1) = V (n + 1) + (((n + 1 + 1 + 5) / 5 : ℕ) : ℤ) := rfl
      have hA : A124502 (n + 1 + 1 + 1) = A124502 (n + 1 + 1) + A124502 (n + 1) +
          (if (n + 2) % 5 = 0 then 1 else 0) := rfl
      rw [hu2, hA, ← h1, ← h0, hv, hu1]
      split_ifs <;> omega

theorem V_sum (n : ℕ) : V n = ∑ k ∈ Finset.Icc 1 n, A124502 k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega), ← ih, ← UA]
    show U n + V n = V n + U n
    ring

theorem Vrec (m : ℕ) :
    V (m + 8) - 2 * V (m + 7) + V (m + 5) - V (m + 3) + 2 * V (m + 2) - V m = 0 := by
  have h6 : V (m + 8) = V (m + 7) + V (m + 6) + (((m + 7 + 5) / 5 : ℕ) : ℤ) := w (m + 6)
  have h5 : V (m + 7) = V (m + 6) + V (m + 5) + (((m + 6 + 5) / 5 : ℕ) : ℤ) := w (m + 5)
  have h1 : V (m + 3) = V (m + 2) + V (m + 1) + (((m + 2 + 5) / 5 : ℕ) : ℤ) := w (m + 1)
  have h0 : V (m + 2) = V (m + 1) + V m + (((m + 1 + 5) / 5 : ℕ) : ℤ) := w m
  omega

end OMAA192759Helpers

namespace OMAA192759PS
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

end OMAA192759PS

open PowerSeries OMAA192759Helpers OMAA192759PS in
theorem OMA.solution : type_of% @OMA.S_oeis_a192759.main := by
  refine ⟨?_, fun n => by rw [a_eq_V, V_sum]⟩
  have hfun : OMA.S_oeis_a192759.a = V := funext a_eq_V
  rw [hfun]
  ext n
  have hD : ((X ^ 2 + X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X - 1) ^ 2 : PowerSeries ℤ) =
      X ^ 8 - C 2 * X ^ 6 + X ^ 5 - X ^ 3 + C 2 * X ^ 1 - X ^ 0 := by
    rw [map_ofNat C 2]; ring
  have hN : (-X : PowerSeries ℤ) = -X ^ 1 := by ring
  rw [hD, hN]
  have v0 : V 0 = 0 := by decide
  have v1 : V 1 = 1 := by decide
  have v2 : V 2 = 2 := by decide
  have v3 : V 3 = 4 := by decide
  have v4 : V 4 = 7 := by decide
  have v5 : V 5 = 12 := by decide
  have v6 : V 6 = 21 := by decide
  have v7 : V 7 = 35 := by decide
  rcases Nat.lt_or_ge n 8 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, map_neg, coeff_mk_mul_C_X_pow,
      coeff_mk_mul_X_pow, coeff_X_pow]
    interval_cases n
    · norm_num [v0]
    · norm_num [v0, v1]
    · norm_num [v0, v1, v2]
    · norm_num [v0, v2, v3]
    · norm_num [v1, v3, v4]
    · norm_num [v0, v2, v4, v5]
    · norm_num [v0, v1, v3, v5, v6]
    · norm_num [v1, v2, v4, v6, v7]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub, map_neg]
    rw [coeff_at V (m + 8) 8 m (by omega), coeff_at_C V 2 (m + 8) 6 (m + 2) (by omega),
      coeff_at V (m + 8) 5 (m + 3) (by omega), coeff_at V (m + 8) 3 (m + 5) (by omega),
      coeff_at_C V 2 (m + 8) 1 (m + 7) (by omega), coeff_at V (m + 8) 0 (m + 8) (by omega),
      coeff_X_pow, if_neg (by omega)]
    linear_combination -(Vrec m)
