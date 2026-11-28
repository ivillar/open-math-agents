import OMAStatements.S_oeis_a025175
import Mathlib

/-!
Credit: @ivillar
Proof: S is (1 + x)^(1/2) composed with R - 1, so S^2 = R and R (2 S') = R' S. Let H be the
g.f. and V = 6H - 1. Since 6 - 24x + 96x^2 = 6R, we get V R = M S with M = -1 + 2x.
Differentiating this and using the equation for S' gives R (2 M R V' - 24x V) = 0, so
M R V' = 12x V, i.e. -(k + 1) v(k + 1) + 6k v(k) - (24k - 12) v(k - 1) + 32 (k - 2) v(k - 2) = 0
for v(k) = [x^k] V. Since v(k + 2) = 6 a(k), the relation at k = n + 1 is -6 times the
conjectured recurrence.
-/

namespace OMAA025175Helpers
open OMA.S_oeis_a025175 PowerSeries

theorem hSR : S ^ 2 = R := by
  have hR : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow hR, sq, ← binomialSeries_add,
    show (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) by norm_num, binomialSeries_nat, pow_one,
    ← coe_substAlgHom hR, map_add, map_one, coe_substAlgHom hR, subst_X hR]
  ring

noncomputable def H : ℚ⟦X⟧ :=
  (1 - 4 * X + 16 * X ^ 2 + (-1 + 2 * X) * S) * (6 - 24 * X + 96 * X ^ 2 : PowerSeries ℚ)⁻¹

noncomputable def V : ℚ⟦X⟧ := 6 * H - 1

theorem hH : H * (6 - 24 * X + 96 * X ^ 2) = 1 - 4 * X + 16 * X ^ 2 + (-1 + 2 * X) * S := by
  have hne : constantCoeff (6 - 24 * X + 96 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    rw [show (6 - 24 * X + 96 * X ^ 2 : ℚ⟦X⟧) = C 6 - C 24 * X + C 96 * X ^ 2 by
      rw [map_ofNat C 6, map_ofNat C 24, map_ofNat C 96], map_add, map_sub, constantCoeff_C,
      map_mul, map_mul, constantCoeff_X, map_pow, constantCoeff_X]
    norm_num
  unfold H
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hne, mul_one]

theorem hV : V * (1 - 4 * X + 16 * X ^ 2) = (-1 + 2 * X) * S := by
  unfold V
  linear_combination hH

theorem dS : (1 - 4 * X + 16 * X ^ 2) * (2 * d⁄dX ℚ S) = (-4 + 32 * X) * S := by
  have h1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
    rw [derivative_pow]; norm_num
  have h2 : d⁄dX ℚ (1 - C 4 * X + C 16 * X ^ 2 : ℚ⟦X⟧) = -(C 4) + C 32 * X := by
    ext k
    rw [coeff_derivative]
    rcases k with _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C]
    norm_num
  rw [map_ofNat C 4, map_ofNat C 16, map_ofNat C 32] at h2
  have hS2 : S ^ 2 = 1 - 4 * X + 16 * X ^ 2 := by rw [hSR, R]
  rw [show (-4 + 32 * X : ℚ⟦X⟧) = -(4 : ℚ⟦X⟧) + 32 * X by ring, ← h2, ← hS2, h1]
  ring

theorem ode : 2 * ((-1 + 6 * X - 24 * X ^ 2 + 32 * X ^ 3) * d⁄dX ℚ V) - 24 * X * V = 0 := by
  have hR' : d⁄dX ℚ (1 - C 4 * X + C 16 * X ^ 2 : ℚ⟦X⟧) = -(C 4) + C 32 * X := by
    ext k
    rw [coeff_derivative]
    rcases k with _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C]
    norm_num
  have hM' : d⁄dX ℚ (-1 + C 2 * X : ℚ⟦X⟧) = C 2 := by
    ext k
    rw [coeff_derivative]
    rcases k with _ | k <;> simp [coeff_one, coeff_C]
  have hV' : V * (1 - C 4 * X + C 16 * X ^ 2) = (-1 + C 2 * X) * S := by
    rw [map_ofNat C 4, map_ofNat C 16, map_ofNat C 2]
    exact hV
  have hd := congrArg (d⁄dX ℚ) hV'
  rw [Derivation.leibniz, Derivation.leibniz, hR', hM', smul_eq_mul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul] at hd
  rw [map_ofNat C 4, map_ofNat C 16, map_ofNat C 2, map_ofNat C 32] at hd
  have hq : (1 - 4 * X + 16 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  have key : (1 - 4 * X + 16 * X ^ 2) *
      (2 * ((-1 + 6 * X - 24 * X ^ 2 + 32 * X ^ 3) * d⁄dX ℚ V) - 24 * X * V) = 0 := by
    linear_combination (2 * (-1 + 2 * X) * (1 - 4 * X + 16 * X ^ 2)) * hd
      + (-1 + 2 * X) ^ 2 * dS
      - (2 * 2 * (1 - 4 * X + 16 * X ^ 2) + (-1 + 2 * X) * (-4 + 32 * X)) * hV
  exact (mul_eq_zero.mp key).resolve_left hq

theorem T (j i1 i2 i3 i4 : ℕ) (h1 : i1 = j + 1) (h2 : i2 = j + 1 + 1)
    (h3 : i3 = j + 1 + 1 + 1) (h4 : i4 = j + 1 + 1 + 1 + 1) :
    -2 * ((j : ℚ) + 4) * coeff i4 V + 12 * ((j : ℚ) + 3) * coeff i3 V
      - 48 * ((j : ℚ) + 2) * coeff i2 V + 64 * ((j : ℚ) + 1) * coeff i1 V
      - 24 * coeff i2 V = 0 := by
  subst h1 h2 h3 h4
  have o := ode
  rw [← map_ofNat C 2, ← map_ofNat C 6, ← map_ofNat C 24, ← map_ofNat C 32] at o
  have e : C 2 * ((-1 + C 6 * X - C 24 * X ^ 2 + C 32 * X ^ 3) * d⁄dX ℚ V) - C 24 * X * V =
      -(C 2 * d⁄dX ℚ V) + C 2 * (C 6 * (X * d⁄dX ℚ V))
        - C 2 * (C 24 * (X * (X * d⁄dX ℚ V)))
        + C 2 * (C 32 * (X * (X * (X * d⁄dX ℚ V)))) - C 24 * (X * V) := by ring
  rw [e] at o
  have h := congrArg (coeff (j + 1 + 1 + 1)) o
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_succ_X_mul, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

theorem hv (k i : ℕ) (hi : i = k + 2) : coeff i V = 6 * a k := by
  subst hi
  have e : V = C 6 * H - 1 := by
    unfold V
    rw [map_ofNat C 6]
  rw [e, map_sub, coeff_C_mul, coeff_one, if_neg (by omega),
    show a k = coeff (k + 2) H from rfl]
  ring

end OMAA025175Helpers

open OMAA025175Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a025175.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  push_cast
  have t := T (m + 1) (m + 2) (m + 3) (m + 4) (m + 5) (by omega) (by omega) (by omega)
    (by omega)
  have g5 := hv (m + 3) (m + 5) (by omega)
  have g4 := hv (m + 2) (m + 4) (by omega)
  have g3 := hv (m + 1) (m + 3) (by omega)
  have g2 := hv m (m + 2) (by omega)
  push_cast at t
  linear_combination (-1 / 12 : ℚ) * t - (((m : ℚ) + 5) / 6) * g5 + ((m : ℚ) + 4) * g4
    - (4 * (m : ℚ) + 14) * g3 + (16 * ((m : ℚ) + 2) / 3) * g2
