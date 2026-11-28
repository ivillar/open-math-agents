import OMAStatements.S_oeis_a128723
import Mathlib

/-!
Credit: @ivillar
Proof: S is (1 + x)^(1/2) composed with R - 1, so S^2 = R (binomialSeries_add and
binomialSeries_nat). Differentiating and multiplying by S gives R (2 S') = R' S, so
(k + 1) s(k + 1) - (6k - 3) s(k) + (5k - 10) s(k - 1) = 0 for s(k) = [x^k] S. Multiplying the
g.f. by 3 + x gives s(k) = -(3 a(k - 1) + a(k - 2)) for k >= 3, and substituting this into
the relation at k = n gives the conjectured recurrence.
-/

namespace OMAA128723Helpers
open OMA.S_oeis_a128723 PowerSeries

theorem hSR : S ^ 2 = R := by
  have hR : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow hR, sq, ← binomialSeries_add,
    show (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) by norm_num, binomialSeries_nat, pow_one,
    ← coe_substAlgHom hR, map_add, map_one, coe_substAlgHom hR, subst_X hR]
  ring

theorem hS : S ^ 2 = 1 - C 6 * X + C 5 * X ^ 2 := by
  rw [hSR, R, map_ofNat C 6, map_ofNat C 5]

theorem h1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
  rw [derivative_pow]; norm_num

theorem h2 : d⁄dX ℚ (1 - C 6 * X + C 5 * X ^ 2 : ℚ⟦X⟧) = -(C 6) + C 10 * X := by
  ext k
  rw [coeff_derivative]
  rcases k with _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C]
  norm_num

theorem E0 : (1 - C 6 * X + C 5 * X ^ 2) * (C 2 * d⁄dX ℚ S) = (-(C 6) + C 10 * X) * S := by
  rw [← h2, ← hS, h1, map_ofNat C 2]
  ring

theorem T (j i1 i2 i3 : ℕ) (h1 : i1 = j + 1) (h2 : i2 = j + 1 + 1) (h3 : i3 = j + 1 + 1 + 1) :
    2 * ((j : ℚ) + 3) * coeff i3 S - 12 * ((j : ℚ) + 2) * coeff i2 S
      + 10 * ((j : ℚ) + 1) * coeff i1 S = -6 * coeff i2 S + 10 * coeff i1 S := by
  subst h1 h2 h3
  have h := congrArg (coeff (j + 1 + 1)) E0
  have eL : (1 - C 6 * X + C 5 * X ^ 2) * (C 2 * d⁄dX ℚ S) =
      C 2 * d⁄dX ℚ S - C 6 * (C 2 * (X * d⁄dX ℚ S)) + C 5 * (C 2 * (X * (X * d⁄dX ℚ S))) := by
    ring
  have eR : (-(C 6) + C 10 * X) * S = -(C 6 * S) + C 10 * (X * S) := by ring
  rw [eL, eR] at h
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at h
  push_cast at h
  linear_combination h

theorem hs (k i i2 i1 : ℕ) (hi : i = k + 1 + 1 + 1) (hi2 : i2 = k + 1 + 1) (hi1 : i1 = k + 1) :
    coeff i S = -3 * a i2 - a i1 := by
  subst hi hi2 hi1
  have hne : constantCoeff (3 + X : ℚ⟦X⟧) ≠ 0 := by
    rw [show (3 + X : ℚ⟦X⟧) = C 3 + X by rw [map_ofNat C 3], map_add, constantCoeff_C,
      constantCoeff_X]
    norm_num
  have e : (1 - X ^ 2 - S) * (3 + X : PowerSeries ℚ)⁻¹ * (3 + X) = 1 - X ^ 2 - S := by
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hne, mul_one]
  have e2 : C 3 * ((1 - X ^ 2 - S) * (3 + X : PowerSeries ℚ)⁻¹)
      + X * ((1 - X ^ 2 - S) * (3 + X : PowerSeries ℚ)⁻¹) = 1 - X ^ 2 - S := by
    rw [map_ofNat C 3]
    linear_combination e
  have h := congrArg (coeff (k + 1 + 1 + 1)) e2
  rw [map_add, coeff_C_mul, coeff_succ_X_mul, map_sub, map_sub, coeff_one, coeff_X_pow,
    if_neg (by omega), if_neg (by omega)] at h
  rw [show a (k + 1 + 1) = coeff (k + 1 + 1 + 1) ((1 - X ^ 2 - S) * (3 + X : PowerSeries ℚ)⁻¹)
      from rfl,
    show a (k + 1) = coeff (k + 1 + 1) ((1 - X ^ 2 - S) * (3 + X : PowerSeries ℚ)⁻¹) from rfl]
  linear_combination h

end OMAA128723Helpers

open OMAA128723Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a128723.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  push_cast
  have t := T (m + 2) (m + 3) (m + 4) (m + 5) (by omega) (by omega) (by omega)
  have g5 := hs (m + 2) (m + 5) (m + 4) (m + 3) (by omega) (by omega) (by omega)
  have g4 := hs (m + 1) (m + 4) (m + 3) (m + 2) (by omega) (by omega) (by omega)
  have g3 := hs m (m + 3) (m + 2) (m + 1) (by omega) (by omega) (by omega)
  push_cast at t
  linear_combination (-1 / 2 : ℚ) * t + ((m : ℚ) + 5) * g5 - (6 * (m : ℚ) + 21) * g4
    + (5 * (m : ℚ) + 10) * g3
