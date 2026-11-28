import OMAStatements.S_oeis_a114589
import Mathlib

/-!
Credit: @ivillar
Proof: S is (1 + x)^(1/2) composed with R - 1, so S^2 = R (binomialSeries_add and
binomialSeries_nat). Differentiating and multiplying by S gives R (2 S') = R' S, so
(k + 1) s(k + 1) - (2k - 1) s(k) - (3k - 6) s(k - 1) = 0 for s(k) = [x^k] S. Multiplying the
g.f. by 4 + 4x + 2x^2 gives s(p + 6) = -(4 a(p + 2) + 4 a(p + 1) + 2 a(p)), and substituting
this into the relation at k = n + 3 gives the conjectured recurrence (times -4).
-/

namespace OMAA114589Helpers
open OMA.S_oeis_a114589 PowerSeries

theorem hSR : S ^ 2 = R := by
  have hR : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow hR, sq, ← binomialSeries_add,
    show (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) by norm_num, binomialSeries_nat, pow_one,
    ← coe_substAlgHom hR, map_add, map_one, coe_substAlgHom hR, subst_X hR]
  ring

theorem hS : S ^ 2 = 1 - C 2 * X - C 3 * X ^ 2 := by
  rw [hSR, R, map_ofNat C 2, map_ofNat C 3]

theorem h1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
  rw [derivative_pow]; norm_num

theorem h2 : d⁄dX ℚ (1 - C 2 * X - C 3 * X ^ 2 : ℚ⟦X⟧) = -(C 2) - C 6 * X := by
  ext k
  rw [coeff_derivative]
  rcases k with _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C]
  norm_num

theorem E0 : (1 - C 2 * X - C 3 * X ^ 2) * (C 2 * d⁄dX ℚ S) = (-(C 2) - C 6 * X) * S := by
  rw [← h2, ← hS, h1, map_ofNat C 2]
  ring

theorem T (j i1 i2 i3 : ℕ) (h1 : i1 = j + 1) (h2 : i2 = j + 1 + 1) (h3 : i3 = j + 1 + 1 + 1) :
    2 * ((j : ℚ) + 3) * coeff i3 S - 4 * ((j : ℚ) + 2) * coeff i2 S
      - 6 * ((j : ℚ) + 1) * coeff i1 S = -2 * coeff i2 S - 6 * coeff i1 S := by
  subst h1 h2 h3
  have h := congrArg (coeff (j + 1 + 1)) E0
  have eL : (1 - C 2 * X - C 3 * X ^ 2) * (C 2 * d⁄dX ℚ S) =
      C 2 * d⁄dX ℚ S - C 2 * (C 2 * (X * d⁄dX ℚ S)) - C 3 * (C 2 * (X * (X * d⁄dX ℚ S))) := by
    ring
  have eR : (-(C 2) - C 6 * X) * S = -(C 2 * S) - C 6 * (X * S) := by ring
  rw [eL, eR] at h
  simp only [map_sub, map_neg, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at h
  push_cast at h
  linear_combination h

theorem hs (p i i2 i1 : ℕ) (hi : i = p + 1 + 1 + 1 + 1 + 1 + 1) (hi2 : i2 = p + 1 + 1)
    (hi1 : i1 = p + 1) :
    coeff i S = -4 * a i2 - 4 * a i1 - 2 * a p := by
  subst hi hi2 hi1
  have hne : constantCoeff (4 + 4 * X + 2 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    rw [show (4 + 4 * X + 2 * X ^ 2 : ℚ⟦X⟧) = C 4 + C 4 * X + C 2 * X ^ 2 by
      rw [map_ofNat C 4, map_ofNat C 2], map_add, map_add, constantCoeff_C, map_mul, map_mul,
      constantCoeff_X, map_pow, constantCoeff_X]
    norm_num
  have e : (1 - X - 2 * X ^ 2 - 2 * X ^ 3 - S) * (4 + 4 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹
      * (4 + 4 * X + 2 * X ^ 2) = 1 - X - 2 * X ^ 2 - 2 * X ^ 3 - S := by
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hne, mul_one]
  have e2 : C 4 * ((1 - X - 2 * X ^ 2 - 2 * X ^ 3 - S)
        * (4 + 4 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)
      + C 4 * (X * ((1 - X - 2 * X ^ 2 - 2 * X ^ 3 - S)
        * (4 + 4 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹))
      + C 2 * (X * (X * ((1 - X - 2 * X ^ 2 - 2 * X ^ 3 - S)
        * (4 + 4 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)))
      = 1 - X - C 2 * X ^ 2 - C 2 * X ^ 3 - S := by
    rw [map_ofNat C 4, map_ofNat C 2]
    linear_combination e
  have h := congrArg (coeff (p + 1 + 1 + 1 + 1 + 1 + 1)) e2
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul] at h
  rw [map_sub, map_sub, map_sub, map_sub, coeff_one, coeff_X, coeff_C_mul, coeff_X_pow,
    coeff_C_mul, coeff_X_pow, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)] at h
  rw [show a (p + 1 + 1) = coeff (p + 1 + 1 + 1 + 1 + 1 + 1) ((1 - X - 2 * X ^ 2 - 2 * X ^ 3 - S)
        * (4 + 4 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹) from rfl,
    show a (p + 1) = coeff (p + 1 + 1 + 1 + 1 + 1) ((1 - X - 2 * X ^ 2 - 2 * X ^ 3 - S)
        * (4 + 4 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹) from rfl,
    show a p = coeff (p + 1 + 1 + 1 + 1) ((1 - X - 2 * X ^ 2 - 2 * X ^ 3 - S)
        * (4 + 4 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹) from rfl]
  linear_combination h

end OMAA114589Helpers

open OMAA114589Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a114589.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  push_cast
  have t := T (m + 5) (m + 6) (m + 7) (m + 8) (by omega) (by omega) (by omega)
  have g8 := hs (m + 2) (m + 8) (m + 4) (m + 3) (by omega) (by omega) (by omega)
  have g7 := hs (m + 1) (m + 7) (m + 3) (m + 2) (by omega) (by omega) (by omega)
  have g6 := hs m (m + 6) (m + 2) (m + 1) (by omega) (by omega) (by omega)
  push_cast at t
  linear_combination (-1 / 4 : ℚ) * t + (((m : ℚ) + 8) / 2) * g8
    - ((2 * (m : ℚ) + 13) / 2) * g7 - ((3 * (m : ℚ) + 15) / 2) * g6
