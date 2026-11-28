import OMAStatements.S_oeis_a134389
import Mathlib

/-!
Credit: @ivillar
Proof: S is (1 + x)^(1/2) composed with R - 1, so S^2 = R = 1 - 4x^2 and R (2 S') = -8x S.
Let H be the g.f. and V = (2 - 4x) H - (2 - x). Since 2 - 8x + 8x^2 = 2 (1 - 2x)^2 and
2 - 5x + 2x^2 = (2 - x)(1 - 2x), we get V (1 - 2x) = x S. Differentiating this and using the
equation for S' gives (1 - 2x) (x R V' - (1 + 2x - 4x^2) V) = 0, hence
(k - 1) v(k) - 2 v(k - 1) - (4k - 12) v(k - 2) = 0 for v(k) = [x^k] V. Since
v(k) = 2 a(k) - 4 a(k - 1) for k >= 2, substituting gives twice the conjectured recurrence
(the term with v(k - 2) has coefficient 0 when k = 3).
-/

namespace OMAA134389Helpers
open OMA.S_oeis_a134389 PowerSeries

theorem hSR : S ^ 2 = R := by
  have hR : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow hR, sq, ← binomialSeries_add,
    show (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) by norm_num, binomialSeries_nat, pow_one,
    ← coe_substAlgHom hR, map_add, map_one, coe_substAlgHom hR, subst_X hR]
  ring

noncomputable def H : ℚ⟦X⟧ :=
  (2 - 5 * X + 2 * X ^ 2 + (X) * S) * (2 - 8 * X + 8 * X ^ 2 : PowerSeries ℚ)⁻¹

noncomputable def V : ℚ⟦X⟧ := H * (2 - 4 * X) - (2 - X)

theorem hH : H * (2 - 8 * X + 8 * X ^ 2) = 2 - 5 * X + 2 * X ^ 2 + X * S := by
  have hne : constantCoeff (2 - 8 * X + 8 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    rw [show (2 - 8 * X + 8 * X ^ 2 : ℚ⟦X⟧) = C 2 - C 8 * X + C 8 * X ^ 2 by
      rw [map_ofNat C 2, map_ofNat C 8], map_add, map_sub, constantCoeff_C,
      map_mul, map_mul, constantCoeff_X, map_pow, constantCoeff_X]
    norm_num
  unfold H
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hne, mul_one]

theorem hV : V * (1 - 2 * X) = X * S := by
  unfold V
  linear_combination hH

theorem dS : (1 - 4 * X ^ 2) * (2 * d⁄dX ℚ S) = -(8 * X) * S := by
  have h1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
    rw [derivative_pow]; norm_num
  have h2 : d⁄dX ℚ (1 - C 4 * X ^ 2 : ℚ⟦X⟧) = -(C 8 * X) := by
    ext k
    rw [coeff_derivative]
    rcases k with _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C]
    norm_num
  rw [map_ofNat C 4, map_ofNat C 8] at h2
  have hS2 : S ^ 2 = 1 - 4 * X ^ 2 := by rw [hSR, R]
  rw [← h2, ← hS2, h1]
  ring

theorem ode : 2 * (X * (1 - 4 * X ^ 2) * d⁄dX ℚ V) - 2 * (1 + 2 * X - 4 * X ^ 2) * V = 0 := by
  have h3 : d⁄dX ℚ (1 - C 2 * X : ℚ⟦X⟧) = -(C 2) := by
    ext k
    rw [coeff_derivative]
    rcases k with _ | k <;> simp [coeff_one, coeff_C]
  have hV' : V * (1 - C 2 * X) = X * S := by
    rw [map_ofNat C 2]
    exact hV
  have hd := congrArg (d⁄dX ℚ) hV'
  rw [Derivation.leibniz, Derivation.leibniz, h3, derivative_X, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul] at hd
  rw [map_ofNat C 2] at hd
  have hq : (1 - 2 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  have key : (1 - 2 * X) * (2 * (X * (1 - 4 * X ^ 2) * d⁄dX ℚ V)
      - 2 * (1 + 2 * X - 4 * X ^ 2) * V) = 0 := by
    linear_combination (2 * X * (1 - 4 * X ^ 2)) * hd + X ^ 2 * dS
      - (2 * (1 - 8 * X ^ 2)) * hV
  exact (mul_eq_zero.mp key).resolve_left hq

theorem T (j i1 i2 i3 : ℕ) (h1 : i1 = j + 1) (h2 : i2 = j + 1 + 1) (h3 : i3 = j + 1 + 1 + 1) :
    2 * ((j : ℚ) + 3) * coeff i3 V - 8 * ((j : ℚ) + 1) * coeff i1 V
      - 2 * coeff i3 V - 4 * coeff i2 V + 8 * coeff i1 V = 0 := by
  subst h1 h2 h3
  have o := ode
  rw [← map_ofNat C 2, ← map_ofNat C 4] at o
  have e : C 2 * (X * (1 - C 4 * X ^ 2) * d⁄dX ℚ V) - C 2 * (1 + C 2 * X - C 4 * X ^ 2) * V =
      C 2 * (X * d⁄dX ℚ V) - C 2 * (C 4 * (X * (X * (X * d⁄dX ℚ V))))
        - C 2 * V - C 2 * (C 2 * (X * V)) + C 2 * (C 4 * (X * (X * V))) := by ring
  rw [e] at o
  have h := congrArg (coeff (j + 1 + 1 + 1)) o
  simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_derivative, map_zero] at h
  push_cast at h
  linear_combination h

theorem hv (k i i1 : ℕ) (hi : i = k + 1 + 1) (hi1 : i1 = k + 1) :
    coeff i V = 2 * a i - 4 * a i1 := by
  subst hi hi1
  have e : V = C 2 * H - C 4 * (X * H) - C 2 + X := by
    unfold V
    rw [map_ofNat C 2, map_ofNat C 4]
    ring
  rw [e, map_add, map_sub, map_sub, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul, coeff_C,
    coeff_X, if_neg (by omega), if_neg (by omega),
    show a (k + 1 + 1) = coeff (k + 1 + 1) H from rfl,
    show a (k + 1) = coeff (k + 1) H from rfl]
  ring

end OMAA134389Helpers

open OMAA134389Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a134389.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  push_cast
  have t := T m (m + 1) (m + 2) (m + 3) (by omega) (by omega) (by omega)
  have g3 := hv (m + 1) (m + 3) (m + 2) (by omega) (by omega)
  have g2 := hv m (m + 2) (m + 1) (by omega) (by omega)
  have g0 : (m : ℚ) * coeff (m + 1) OMAA134389Helpers.V =
      (m : ℚ) * (2 * OMA.S_oeis_a134389.a (m + 1) - 4 * OMA.S_oeis_a134389.a m) := by
    rcases m with _ | j
    · simp
    · rw [hv j (j + 1 + 1) (j + 1) (by omega) (by omega)]
  linear_combination (1 / 4 : ℚ) * t - (((m : ℚ) + 2) / 2) * g3 + g2 + 2 * g0
