import OMAStatements.S_oeis_a223907
import Mathlib

/-!
Credit: @ivillar
Proof: the unsigned Stirling numbers of the first kind of row 4 are 0, 6, 11, 6, 1, so
a(n) = 6*2^n + 11*3^n + 6*4^n + 5^n, which is the closed form (2^(1+2n) = 2*4^n). The
denominator is (1-2x)(1-3x)(1-4x)(1-5x) = 1 - 14x + 71x^2 - 154x^3 + 120x^4, which kills each
geometric term, and the first four coefficients give the numerator
74x - 792x^2 + 2692x^3 - 2880x^4.
-/

namespace OMAA223907Helpers
open PowerSeries OMA.S_oeis_a223907

theorem closed (n : ℕ) : a n = 6 * 2 ^ n + 11 * 3 ^ n + 6 * 4 ^ n + 5 ^ n := by
  have s0 : Nat.stirlingFirst 4 0 = 0 := by decide
  have s1 : Nat.stirlingFirst 4 1 = 6 := by decide
  have s2 : Nat.stirlingFirst 4 2 = 11 := by decide
  have s3 : Nat.stirlingFirst 4 3 = 6 := by decide
  have s4 : Nat.stirlingFirst 4 4 = 1 := by decide
  unfold a hatc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, s0, s1, s2, s3, s4]
  push_cast
  ring

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

end OMAA223907Helpers

open PowerSeries OMAA223907Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a223907.main := by
  refine ⟨fun n _ => ?_, ?_⟩
  · rw [closed, show 2 ^ (1 + 2 * n) = 2 * (4 : ℤ) ^ n by rw [pow_add, pow_mul]; norm_num,
      show (2 : ℤ) ^ (1 + n) = 2 * 2 ^ n by rw [pow_add]; norm_num]
    ring
  · set f : ℕ → ℤ := fun n => if n = 0 then 0 else OMA.S_oeis_a223907.a n with hfdef
    have hA : OMA.S_oeis_a223907.A = PowerSeries.mk f := rfl
    rw [hA]
    ext n
    have hD : ((2 * X - 1) * (3 * X - 1) * (4 * X - 1) * (5 * X - 1) : PowerSeries ℤ) =
        X ^ 0 - C 14 * X ^ 1 + C 71 * X ^ 2 - C 154 * X ^ 3 + C 120 * X ^ 4 := by
      rw [map_ofNat C 14, map_ofNat C 71, map_ofNat C 154, map_ofNat C 120]; ring
    have hN : (-2 * X * (1440 * X ^ 3 - 1346 * X ^ 2 + 396 * X - 37) : PowerSeries ℤ) =
        C 74 * X ^ 1 - C 792 * X ^ 2 + C 2692 * X ^ 3 - C 2880 * X ^ 4 := by
      rw [map_ofNat C 74, map_ofNat C 792, map_ofNat C 2692, map_ofNat C 2880]; ring
    rw [hD, hN]
    have hf : ∀ k, f (k + 1) = 6 * 2 ^ (k + 1) + 11 * 3 ^ (k + 1) + 6 * 4 ^ (k + 1) + 5 ^ (k + 1) := by
      intro k
      simp only [hfdef, Nat.add_one_ne_zero, if_false]
      exact closed (k + 1)
    have v0 : f 0 = 0 := by simp [hfdef]
    have v1 : f 1 = 74 := by rw [hf 0]; norm_num
    have v2 : f 2 = 244 := by rw [hf 1]; norm_num
    have v3 : f 3 = 854 := by rw [hf 2]; norm_num
    have v4 : f 4 = 3148 := by rw [hf 3]; norm_num
    rcases Nat.lt_or_ge n 5 with h | h
    · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
        coeff_C_mul, coeff_X_pow]
      interval_cases n
      · norm_num [v0]
      · norm_num [v0, v1]
      · norm_num [v0, v1, v2]
      · norm_num [v0, v1, v2, v3]
      · norm_num [v0, v1, v2, v3, v4]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      simp only [mul_add, mul_sub, map_add, map_sub]
      rw [coeff_at f (m + 5) 0 (m + 4 + 1) (by omega),
        coeff_at_C f 14 (m + 5) 1 (m + 3 + 1) (by omega),
        coeff_at_C f 71 (m + 5) 2 (m + 2 + 1) (by omega),
        coeff_at_C f 154 (m + 5) 3 (m + 1 + 1) (by omega),
        coeff_at_C f 120 (m + 5) 4 (m + 1) (by omega),
        coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X_pow,
        coeff_X_pow, coeff_X_pow, if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), hf, hf, hf, hf, hf]
      ring
