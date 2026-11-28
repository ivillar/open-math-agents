import OMAStatements.S_oeis_a159771
import Mathlib

/-!
Credit: @ivillar
Proof: S is (1 + x)^(1/2) composed with R - 1, so S^2 = R (binomialSeries_add and
binomialSeries_nat). Differentiating and multiplying by S gives R (2 S') = R' S, whose
coefficients give a first-order recurrence for s(k) = [x^k] S. Since 4 a(k) = -s(k + 1) for
k >= 2, the conjectured recurrence at n is minus one eighth of that relation at n - 4,
rewritten in a (the term with a(n - 4) has coefficient 0 when n = 5).
-/

namespace OMAA159771Helpers
open OMA.S_oeis_a159771 PowerSeries

theorem hSR : S ^ 2 = R := by
  have hR : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow hR, sq, ← binomialSeries_add,
    show (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) by norm_num, binomialSeries_nat, pow_one,
    ← coe_substAlgHom hR, map_add, map_one, coe_substAlgHom hR, subst_X hR]
  ring

theorem hS : S ^ 2 = 1 - C 4 * X + C 2 * X ^ 2 - C 4 * X ^ 3 + X ^ 4 := by
  rw [hSR, R, map_ofNat C 4, map_ofNat C 2]

theorem h1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
  rw [derivative_pow]; norm_num

theorem h2 : d⁄dX ℚ (1 - C 4 * X + C 2 * X ^ 2 - C 4 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) =
    -(C 4) + C 4 * X - C 12 * X ^ 2 + C 4 * X ^ 3 := by
  ext k
  rw [coeff_derivative]
  rcases k with _ | _ | _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C] <;> norm_num

theorem E0 : (1 - C 4 * X + C 2 * X ^ 2 - C 4 * X ^ 3 + X ^ 4) * (C 2 * d⁄dX ℚ S) =
    (-(C 4) + C 4 * X - C 12 * X ^ 2 + C 4 * X ^ 3) * S := by
  rw [← h2, ← hS, h1, map_ofNat C 2]
  ring

theorem T (j i1 i2 i3 i4 i5 : ℕ) (h1 : i1 = j + 1) (h2 : i2 = j + 1 + 1)
    (h3 : i3 = j + 1 + 1 + 1) (h4 : i4 = j + 1 + 1 + 1 + 1) (h5 : i5 = j + 1 + 1 + 1 + 1 + 1) :
    2 * ((j : ℚ) + 5) * coeff i5 S - 8 * ((j : ℚ) + 4) * coeff i4 S
      + 4 * ((j : ℚ) + 3) * coeff i3 S - 8 * ((j : ℚ) + 2) * coeff i2 S
      + 2 * ((j : ℚ) + 1) * coeff i1 S
      = -4 * coeff i4 S + 4 * coeff i3 S - 12 * coeff i2 S + 4 * coeff i1 S := by
  subst h1 h2 h3 h4 h5
  have h := congrArg (coeff (j + 1 + 1 + 1 + 1)) E0
  have eL : (1 - C 4 * X + C 2 * X ^ 2 - C 4 * X ^ 3 + X ^ 4) * (C 2 * d⁄dX ℚ S) =
      C 2 * d⁄dX ℚ S - C 4 * (C 2 * (X * d⁄dX ℚ S))
        + C 2 * (C 2 * (X * (X * d⁄dX ℚ S)))
        - C 4 * (C 2 * (X * (X * (X * d⁄dX ℚ S))))
        + C 2 * (X * (X * (X * (X * d⁄dX ℚ S)))) := by ring
  have eR : (-(C 4) + C 4 * X - C 12 * X ^ 2 + C 4 * X ^ 3) * S =
      -(C 4 * S) + C 4 * (X * S) - C 12 * (X * (X * S)) + C 4 * (X * (X * (X * S))) := by
    ring
  rw [eL, eR] at h
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at h
  push_cast at h
  linear_combination h

theorem hs (k i : ℕ) (hk : 2 ≤ k) (hi : i = k + 1) : coeff i S = -4 * a k := by
  subst hi
  have hne : constantCoeff (4 : ℚ⟦X⟧) ≠ 0 := by
    rw [show (4 : ℚ⟦X⟧) = C 4 from (map_ofNat C 4).symm, constantCoeff_C]
    norm_num
  have e : (1 - 2 * X + 3 * X ^ 2 - S) * (4 : PowerSeries ℚ)⁻¹ * 4 =
      1 - 2 * X + 3 * X ^ 2 - S := by
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hne, mul_one]
  have e2 : C 4 * ((1 - 2 * X + 3 * X ^ 2 - S) * (4 : PowerSeries ℚ)⁻¹) =
      1 - C 2 * X + C 3 * X ^ 2 - S := by
    rw [map_ofNat C 4, map_ofNat C 2, map_ofNat C 3]
    linear_combination e
  have h := congrArg (coeff (k + 1)) e2
  rw [coeff_C_mul, map_sub, map_add, map_sub, coeff_one, coeff_C_mul, coeff_C_mul, coeff_X,
    coeff_X_pow, if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
  rw [show a k = coeff (k + 1) ((1 - 2 * X + 3 * X ^ 2 - S) * (4 : PowerSeries ℚ)⁻¹) from rfl]
  linear_combination h

end OMAA159771Helpers

open OMAA159771Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a159771.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
  push_cast
  have t := T (m + 1) (m + 2) (m + 3) (m + 4) (m + 5) (m + 6) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have g6 := hs (m + 5) (m + 6) (by omega) (by omega)
  have g5 := hs (m + 4) (m + 5) (by omega) (by omega)
  have g4 := hs (m + 3) (m + 4) (by omega) (by omega)
  have g3 := hs (m + 2) (m + 3) (by omega) (by omega)
  have g0 : (m : ℚ) * coeff (m + 2) OMA.S_oeis_a159771.S = (m : ℚ) * (-4 * OMA.S_oeis_a159771.a (m + 1)) := by
    rcases m with _ | j
    · simp
    · rw [hs (j + 1 + 1) (j + 1 + 2) (by omega) (by omega)]
  push_cast at t
  linear_combination (-1 / 8 : ℚ) * t + (((m : ℚ) + 6) / 4) * g6
    - ((2 * (m : ℚ) + 9) / 2) * g5 + (((m : ℚ) + 3) / 2) * g4
    - ((2 * (m : ℚ) + 3) / 2) * g3 + (1 / 4 : ℚ) * g0
