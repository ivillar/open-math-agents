import OMAStatements.S_oeis_a274295
import Mathlib

-- Problem: A274295: a(n) = n+binomial(2*n-6,n-3)+binomial(2*n-5,n-3)+binomial(n-1,n-3)+Sum_{i=1..n-3} (binomial(n+i-3,n-3)+2*n-i-5).
-- Upstream: formal-conjectures statements/oeis-a274295.lean (declaration OMA.S_oeis_a274295.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a274295

open OMA.S_oeis_a274295 PowerSeries

theorem hR1 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])

theorem S_sq : S ^ 2 = R := by
  have h : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = 1 + X := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    have h12 : (1 / 2 + 1 / 2 : ℚ) = ((1 : ℕ) : ℚ) := by norm_num
    rw [h12, PowerSeries.binomialSeries_nat, pow_one]
  unfold S
  rw [← coe_substAlgHom hR1, ← map_pow, h, map_add, map_one, substAlgHom_X]
  ring

theorem ode : 2 * R * d⁄dX ℚ S = d⁄dX ℚ R * S := by
  have h := congrArg (d⁄dX ℚ) S_sq
  rw [pow_two, Derivation.leibniz, smul_eq_mul] at h
  rw [← h, ← S_sq]
  ring

theorem hRC : R = C (1 : ℚ) + C (-4 : ℚ) * X ^ 1 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-4 : ℚ) := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-8 : ℚ) * X ^ 1 * d⁄dX ℚ S - (C (-4 : ℚ) * S) = 0 := by
  have h := ode
  rw [hDR, hRC] at h
  simp only [map_one, map_neg, map_ofNat] at h ⊢
  linear_combination h

theorem cx (c : ℚ) (j n : ℕ) (f : ℚ⟦X⟧) (h : j ≤ n) :
    coeff n (C c * X ^ j * f) = c * coeff (n - j) f := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos h]

theorem cx0 (c : ℚ) (n : ℕ) (f : ℚ⟦X⟧) : coeff n (C c * f) = c * coeff n f := coeff_C_mul _ _ _

theorem cc (c : ℚ) (j n : ℕ) (h : n ≠ j) : coeff n (C c * X ^ j) = 0 := by
  rw [coeff_C_mul_X_pow, if_neg h]

theorem cc0 (c : ℚ) (n : ℕ) (h : n ≠ 0) : coeff n (C c : ℚ⟦X⟧) = 0 := by
  rw [coeff_C, if_neg h]

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (-8 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-4 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 1)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 1 - 1 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5 + (X ^ 2 - 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6) * S) * (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff n F := rfl

theorem hF : F * (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4 : ℚ⟦X⟧) = 1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5 + (X ^ 2 - 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4 : ℚ⟦X⟧) = C (1 : ℚ) + C (-7 : ℚ) * X ^ 1 + C (15 : ℚ) * X ^ 2 + C (-13 : ℚ) * X ^ 3 + C (4 : ℚ) * X ^ 4 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (1 : ℚ) * F + C (-7 : ℚ) * X ^ 1 * F + C (15 : ℚ) * X ^ 2 * F + C (-13 : ℚ) * X ^ 3 * F + C (4 : ℚ) * X ^ 4 * F - (C (1 : ℚ) * X ^ 2 * S + C (-2 : ℚ) * X ^ 3 * S + C (2 : ℚ) * X ^ 5 * S + C (-1 : ℚ) * X ^ 6 * S) - (C (1 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (10 : ℚ) * X ^ 2 + C (-9 : ℚ) * X ^ 3 + C (8 : ℚ) * X ^ 4 + C (-16 : ℚ) * X ^ 5) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (1 : ℚ) * coeff (m + 6) F + (-7 : ℚ) * coeff (m + 5) F + (15 : ℚ) * coeff (m + 4) F + (-13 : ℚ) * coeff (m + 3) F + (4 : ℚ) * coeff (m + 2) F - ((1 : ℚ) * coeff (m + 4) S + (-2 : ℚ) * coeff (m + 3) S + (2 : ℚ) * coeff (m + 1) S + (-1 : ℚ) * coeff (m) S) = 0 := by
  have h := congrArg (coeff (m + 6)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 6 - 1 = m + 5 from by omega, show m + 6 - 2 = m + 4 from by omega, show m + 6 - 3 = m + 3 from by omega, show m + 6 - 4 = m + 2 from by omega, show m + 6 - 5 = m + 1 from by omega, show m + 6 - 6 = m from by omega] at h
  linear_combination h

theorem cz (c : ℚ) (j n : ℕ) (f : ℚ⟦X⟧) (h : n < j) : coeff n (C c * X ^ j * f) = 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg (by omega), mul_zero]

theorem ccj (c : ℚ) (j n : ℕ) (h : n = j) : coeff n (C c * X ^ j) = c := by
  rw [coeff_C_mul_X_pow, if_pos h]

theorem cc0' (c : ℚ) : coeff 0 (C c : ℚ⟦X⟧) = c := by rw [coeff_C, if_pos rfl]

theorem S_const : constantCoeff S = 1 := by
  have h0 : constantCoeff (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1) = 0 := by simp
  have hc : constantCoeff (R - 1) = 0 := by simp [R]
  have h1 := constantCoeff_subst_eq_zero (a := (R - 1 : ℚ⟦X⟧)) hc _ h0
  have h2 : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1).subst (R - 1) = S - 1 := by
    unfold S
    rw [← coe_substAlgHom hR1, map_sub, map_one]
  rw [h2] at h1
  have h3 : constantCoeff (S - 1) = 0 := h1
  rw [map_sub, map_one, sub_eq_zero] at h3
  exact h3

theorem hs0 : coeff 0 S = 1 := by rw [coeff_zero_eq_constantCoeff_apply, S_const]

theorem hs1 : coeff 1 S = (-2 : ℚ) := by
  have h := congrArg (coeff 0) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0] at h ⊢ <;> linarith

theorem hs2 : coeff 2 S = (-2 : ℚ) := by
  have h := congrArg (coeff 1) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1] at h ⊢ <;> linarith

theorem hs3 : coeff 3 S = (-4 : ℚ) := by
  have h := congrArg (coeff 2) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2] at h ⊢ <;> linarith

theorem hs4 : coeff 4 S = (-10 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hs5 : coeff 5 S = (-28 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hs6 : coeff 6 S = (-84 : ℚ) := by
  have h := congrArg (coeff 5) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hs7 : coeff 7 S = (-264 : ℚ) := by
  have h := congrArg (coeff 6) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at h ⊢ <;> linarith

theorem hs8 : coeff 8 S = (-858 : ℚ) := by
  have h := congrArg (coeff 7) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h ⊢ <;> linarith

theorem hs9 : coeff 9 S = (-2860 : ℚ) := by
  have h := congrArg (coeff 8) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (1 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (1 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (1 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (3 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (6 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (16 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (43 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (120 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (369 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (1244 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem hf9 : coeff 9 F = (4449 : ℚ) := by
  have h := congrArg (coeff 9) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (1 : ℚ) := by rw [a_eq]; exact hf0

theorem ha1 : a 1 = (1 : ℚ) := by rw [a_eq]; exact hf1

theorem ha2 : a 2 = (3 : ℚ) := by rw [a_eq]; exact hf2

theorem ha3 : a 3 = (6 : ℚ) := by rw [a_eq]; exact hf3

theorem ha4 : a 4 = (16 : ℚ) := by rw [a_eq]; exact hf4

theorem ha5 : a 5 = (43 : ℚ) := by rw [a_eq]; exact hf5

theorem ha6 : a 6 = (120 : ℚ) := by rw [a_eq]; exact hf6

theorem ha7 : a 7 = (369 : ℚ) := by rw [a_eq]; exact hf7

theorem ha8 : a 8 = (1244 : ℚ) := by rw [a_eq]; exact hf8

theorem ha9 : a 9 = (4449 : ℚ) := by rw [a_eq]; exact hf9

noncomputable def Mv (n : ℕ) : ℚ := (-(n : ℚ) + 2) * a n + (7 * (n : ℚ) - 18) * a (n - 1) + (-14 * (n : ℚ) + 42) * a (n - 2)
      + (6 * (n : ℚ) - 4) * a (n - 3) + (11 * (n : ℚ) - 90) * a (n - 4)
      + (-13 * (n : ℚ) + 102) * a (n - 5) + (4 * (n : ℚ) - 34) * a (n - 6)

theorem base8 : Mv 8 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem base9 : Mv 9 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem certQ (k : ℕ) : ((8 : ℚ)) * Mv (k + 9) + ((-2 : ℚ)) * Mv (k + 10) = 0 := by
  unfold Mv
  rw [show k + 9 - 1 = k + 8 from by omega, show k + 9 - 2 = k + 7 from by omega, show k + 9 - 3 = k + 6 from by omega, show k + 9 - 4 = k + 5 from by omega, show k + 9 - 5 = k + 4 from by omega, show k + 9 - 6 = k + 3 from by omega, show k + 10 - 1 = k + 9 from by omega, show k + 10 - 2 = k + 8 from by omega, show k + 10 - 3 = k + 7 from by omega, show k + 10 - 4 = k + 6 from by omega, show k + 10 - 5 = k + 5 from by omega, show k + 10 - 6 = k + 4 from by omega]
  simp only [a_eq]
  have r1_48 := rel1 (k + 1)
  have r1_49 := rel1 (k + 2)
  have r1_50 := rel1 (k + 3)
  have r1_51 := rel1 (k + 4)
  have r2_42 := rel2 (k)
  have r2_43 := rel2 (k + 1)
  have r2_44 := rel2 (k + 2)
  have r2_45 := rel2 (k + 3)
  have r2_46 := rel2 (k + 4)
  have r2_47 := rel2 (k + 5)
  have r2_48 := rel2 (k + 6)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_48 r1_49 r1_50 r1_51 r2_42 r2_43 r2_44 r2_45 r2_46 r2_47 r2_48 ⊢
  push_cast at r1_48 r1_49 r1_50 r1_51 r2_42 r2_43 r2_44 r2_45 r2_46 r2_47 r2_48 ⊢
  linear_combination ((-68 : ℚ) + (8 : ℚ) * ((k : ℚ) + 9) ^ 1) * r1_48 + ((-2 : ℚ) + (-2 : ℚ) * ((k : ℚ) + 9) ^ 1) * r1_49 + ((24 : ℚ) + (-8 : ℚ) * ((k : ℚ) + 9) ^ 1) * r1_50 + ((-2 : ℚ) + (2 : ℚ) * ((k : ℚ) + 9) ^ 1) * r1_51 + ((1 : ℚ)) * r2_42 + ((-2 : ℚ)) * r2_43 + ((-1 : ℚ)) * r2_44 + ((4 : ℚ)) * r2_45 + ((-1 : ℚ)) * r2_46 + ((-2 : ℚ)) * r2_47 + ((1 : ℚ)) * r2_48

theorem Mv_zero : ∀ n : ℕ, 8 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 10
    · interval_cases n
      · exact base8
      · exact base9
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 9) = 0 := ih _ (by omega) (by omega)
      have hq : ((-2 : ℚ)) ≠ 0 := by
        have e : ((-2 : ℚ)) = -((2 : ℚ)) := by ring
        rw [e, neg_ne_zero]
        positivity
      have hm : ((-2 : ℚ)) * Mv (k + 10) = 0 := by linear_combination hc - ((8 : ℚ)) * h0
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 8 ≤ n → (-(n : ℚ) + 2) * a n + (7 * (n : ℚ) - 18) * a (n - 1) + (-14 * (n : ℚ) + 42) * a (n - 2)
      + (6 * (n : ℚ) - 4) * a (n - 3) + (11 * (n : ℚ) - 90) * a (n - 4)
      + (-13 * (n : ℚ) + 102) * a (n - 5) + (4 * (n : ℚ) - 34) * a (n - 6) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a274295

theorem OMA.solution : type_of% @OMA.S_oeis_a274295.main := OMA.P_oeis_a274295.main'
