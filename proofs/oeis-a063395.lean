import OMAStatements.S_oeis_a063395
import Mathlib

/-!
Credit: @ivillar
Proof: S is (1 + x)^(1/2) composed with R - 1, so S^2 = R = (1 - x)(1 - 9x) and
R (2 S') = R' S. Let H be the g.f. and V = (1 - x) H - (1 - 2x). Since
1 - 11x + 18x^2 = (1 - 2x)(1 - 9x), we get V (1 - 9x) = 4x S. Differentiating this and using
the equation for S' gives (1 - 9x) (x R V' - (1 - 6x + 9x^2) V) = 0, hence
(k - 1) v(k) - (10k - 16) v(k - 1) + (9k - 27) v(k - 2) = 0 for v(k) = [x^k] V. Since
v(k) = a(k) - a(k - 1) for k >= 2, substituting gives minus the conjectured recurrence (the term
with v(k - 2) has coefficient 0 when k = 3).
-/

namespace OMAA063395Helpers
open OMA.S_oeis_a063395 PowerSeries

theorem hSR : S ^ 2 = R := by
  have hR : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow hR, sq, ← binomialSeries_add,
    show (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) by norm_num, binomialSeries_nat, pow_one,
    ← coe_substAlgHom hR, map_add, map_one, coe_substAlgHom hR, subst_X hR]
  ring

noncomputable def H : ℚ⟦X⟧ :=
  (1 - 11 * X + 18 * X ^ 2 + (4 * X) * S) * (1 - 10 * X + 9 * X ^ 2 : PowerSeries ℚ)⁻¹

noncomputable def V : ℚ⟦X⟧ := H * (1 - X) - (1 - 2 * X)

theorem hH : H * (1 - 10 * X + 9 * X ^ 2) = 1 - 11 * X + 18 * X ^ 2 + (4 * X) * S := by
  have hne : constantCoeff (1 - 10 * X + 9 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    rw [show (1 - 10 * X + 9 * X ^ 2 : ℚ⟦X⟧) = 1 - C 10 * X + C 9 * X ^ 2 by
      rw [map_ofNat C 10, map_ofNat C 9], map_add, map_sub, map_one,
      map_mul, map_mul, constantCoeff_X, map_pow, constantCoeff_X]
    norm_num
  unfold H
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hne, mul_one]

theorem hV : V * (1 - 9 * X) = 4 * X * S := by
  unfold V
  linear_combination hH

theorem dS : (1 - 10 * X + 9 * X ^ 2) * (2 * d⁄dX ℚ S) = (-10 + 18 * X) * S := by
  have h1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
    rw [derivative_pow]; norm_num
  have h2 : d⁄dX ℚ (1 - C 10 * X + C 9 * X ^ 2 : ℚ⟦X⟧) = -(C 10) + C 18 * X := by
    ext k
    rw [coeff_derivative]
    rcases k with _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C]
    norm_num
  rw [map_ofNat C 10, map_ofNat C 9, map_ofNat C 18] at h2
  have hS2 : S ^ 2 = 1 - 10 * X + 9 * X ^ 2 := by rw [hSR, R]
  rw [show (-10 + 18 * X : ℚ⟦X⟧) = -(10 : ℚ⟦X⟧) + 18 * X by ring, ← h2, ← hS2, h1]
  ring

theorem ode : 2 * (X * (1 - 10 * X + 9 * X ^ 2) * d⁄dX ℚ V)
    - 2 * (1 - 6 * X + 9 * X ^ 2) * V = 0 := by
  have h3 : d⁄dX ℚ (1 - C 9 * X : ℚ⟦X⟧) = -(C 9) := by
    ext k
    rw [coeff_derivative]
    rcases k with _ | k <;> simp [coeff_one, coeff_C]
  have h4 : d⁄dX ℚ (C 4 * X : ℚ⟦X⟧) = C 4 := by
    rw [Derivation.leibniz, derivative_X, derivative_C, smul_zero, add_zero, smul_eq_mul,
      mul_one]
  have hV' : V * (1 - C 9 * X) = C 4 * X * S := by
    rw [map_ofNat C 9, map_ofNat C 4]
    exact hV
  have hd := congrArg (d⁄dX ℚ) hV'
  rw [Derivation.leibniz, Derivation.leibniz, h3, h4, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul] at hd
  rw [map_ofNat C 9, map_ofNat C 4] at hd
  have hq : (1 - 9 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  have key : (1 - 9 * X) * (2 * (X * (1 - 10 * X + 9 * X ^ 2) * d⁄dX ℚ V)
      - 2 * (1 - 6 * X + 9 * X ^ 2) * V) = 0 := by
    linear_combination (2 * X * (1 - 10 * X + 9 * X ^ 2)) * hd + (4 * X ^ 2) * dS
      - (X * (-10 + 18 * X) + 2 * (1 - 10 * X + 9 * X ^ 2)) * hV
  exact (mul_eq_zero.mp key).resolve_left hq

theorem T (j i1 i2 i3 : ℕ) (h1 : i1 = j + 1) (h2 : i2 = j + 1 + 1) (h3 : i3 = j + 1 + 1 + 1) :
    2 * ((j : ℚ) + 3) * coeff i3 V - 20 * ((j : ℚ) + 2) * coeff i2 V
      + 18 * ((j : ℚ) + 1) * coeff i1 V - 2 * coeff i3 V + 12 * coeff i2 V
      - 18 * coeff i1 V = 0 := by
  subst h1 h2 h3
  have o := ode
  rw [← map_ofNat C 2, ← map_ofNat C 10, ← map_ofNat C 9, ← map_ofNat C 6] at o
  have e : C 2 * (X * (1 - C 10 * X + C 9 * X ^ 2) * d⁄dX ℚ V)
      - C 2 * (1 - C 6 * X + C 9 * X ^ 2) * V =
      C 2 * (X * d⁄dX ℚ V) - C 2 * (C 10 * (X * (X * d⁄dX ℚ V)))
        + C 2 * (C 9 * (X * (X * (X * d⁄dX ℚ V))))
        - C 2 * V + C 2 * (C 6 * (X * V)) - C 2 * (C 9 * (X * (X * V))) := by ring
  rw [e] at o
  have h := congrArg (coeff (j + 1 + 1 + 1)) o
  simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_derivative, map_zero] at h
  push_cast at h
  linear_combination h

theorem hv (k i i1 : ℕ) (hi : i = k + 1 + 1) (hi1 : i1 = k + 1) :
    coeff i V = a i - a i1 := by
  subst hi hi1
  have e : V = H - X * H - 1 + C 2 * X := by
    unfold V
    rw [map_ofNat C 2]
    ring
  rw [e, map_add, map_sub, map_sub, coeff_succ_X_mul, coeff_C_mul, coeff_one, coeff_X,
    if_neg (by omega), if_neg (by omega),
    show a (k + 1 + 1) = coeff (k + 1 + 1) H from rfl,
    show a (k + 1) = coeff (k + 1) H from rfl]
  ring

end OMAA063395Helpers

open OMAA063395Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a063395.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  push_cast
  have t := T m (m + 1) (m + 2) (m + 3) (by omega) (by omega) (by omega)
  have g3 := hv (m + 1) (m + 3) (m + 2) (by omega) (by omega)
  have g2 := hv m (m + 2) (m + 1) (by omega) (by omega)
  have g0 : (m : ℚ) * coeff (m + 1) OMAA063395Helpers.V =
      (m : ℚ) * (OMA.S_oeis_a063395.a (m + 1) - OMA.S_oeis_a063395.a m) := by
    rcases m with _ | j
    · simp
    · rw [hv j (j + 1 + 1) (j + 1) (by omega) (by omega)]
  linear_combination (-1 / 2 : ℚ) * t + ((m : ℚ) + 2) * g3 - (10 * (m : ℚ) + 14) * g2
    + 9 * g0
