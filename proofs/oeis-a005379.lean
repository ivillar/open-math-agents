import OMAStatements.S_oeis_a005379
import Mathlib

/-!
Credit: @ivillar
Disproof (Sahand Saba's counterexample at coefficient 33): the denominator is
(1 - x^8)(1 - x) = 1 - x - x^8 + x^9, so the coefficient of x^33 of the left-hand side is
M(33) - M(32) - M(25) + M(24) = 20 - 20 - 16 + 15 = -1, while the right-hand side
x^2 + x^3 + x^5 + x^6 + x^8 + x^9 - x^10 has coefficient 0 at x^33.
-/

open PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a005379.main) := by
  intro h
  have h33 := congrArg (coeff 33) h
  have hD : ((1 - X ^ 8) * (1 - X) : PowerSeries ℤ) = X ^ 0 - X ^ 1 - X ^ 8 + X ^ 9 := by
    ring
  have hN : (X ^ 2 * (1 + X ^ 3 + X ^ 6 + X + X ^ 4 + X ^ 7 - X ^ 8) : PowerSeries ℤ) =
      X ^ 2 + X ^ 5 + X ^ 8 + X ^ 3 + X ^ 6 + X ^ 9 - X ^ 10 := by
    ring
  have v33 : OMA.S_oeis_a005379.a 33 = 20 := by decide +kernel
  have v32 : OMA.S_oeis_a005379.a 32 = 20 := by decide +kernel
  have v25 : OMA.S_oeis_a005379.a 25 = 16 := by decide +kernel
  have v24 : OMA.S_oeis_a005379.a 24 = 15 := by decide +kernel
  rw [hD, hN] at h33
  unfold OMA.S_oeis_a005379.gf at h33
  simp only [mul_add, mul_sub, map_add, map_sub, coeff_mul_X_pow', coeff_mk,
    coeff_X_pow, v33, v32, v25, v24] at h33
  norm_num at h33
