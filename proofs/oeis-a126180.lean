import OMAStatements.S_oeis_a126180
import Mathlib

-- Problem: A126180: Number of branches in all hex trees with n edges (n>=1).
-- Upstream: formal-conjectures statements/oeis-a126180.lean (declaration OMA.S_oeis_a126180.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a126180

open OMA.S_oeis_a126180 PowerSeries

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

theorem hRC : R = C (1 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (5 : ℚ) * X ^ 2 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-6 : ℚ) + C (10 : ℚ) * X ^ 1 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-12 : ℚ) * X ^ 1 * d⁄dX ℚ S + C (10 : ℚ) * X ^ 2 * d⁄dX ℚ S - (C (-6 : ℚ) * S + C (10 : ℚ) * X ^ 1 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (-12 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (10 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-6 : ℚ) * coeff (m + 2) S + (10 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 2)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((-2 + 21 * X - 73 * X ^ 2 + 99 * X ^ 3 - 45 * X ^ 4 + (2 - 15 * X + 32 * X ^ 2 - 15 * X ^ 3) * S) * (2 - 12 * X + 10 * X ^ 2 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff (n + 2) F := rfl

theorem hF : F * (2 - 12 * X + 10 * X ^ 2 : ℚ⟦X⟧) = -2 + 21 * X - 73 * X ^ 2 + 99 * X ^ 3 - 45 * X ^ 4 + (2 - 15 * X + 32 * X ^ 2 - 15 * X ^ 3) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 - 12 * X + 10 * X ^ 2 : ℚ⟦X⟧) = C (2 : ℚ) + C (-12 : ℚ) * X ^ 1 + C (10 : ℚ) * X ^ 2 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (-12 : ℚ) * X ^ 1 * F + C (10 : ℚ) * X ^ 2 * F - (C (2 : ℚ) * S + C (-15 : ℚ) * X ^ 1 * S + C (32 : ℚ) * X ^ 2 * S + C (-15 : ℚ) * X ^ 3 * S) - (C (-2 : ℚ) + C (21 : ℚ) * X ^ 1 + C (-73 : ℚ) * X ^ 2 + C (99 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 5) F + (-12 : ℚ) * coeff (m + 4) F + (10 : ℚ) * coeff (m + 3) F - ((2 : ℚ) * coeff (m + 5) S + (-15 : ℚ) * coeff (m + 4) S + (32 : ℚ) * coeff (m + 3) S + (-15 : ℚ) * coeff (m + 2) S) = 0 := by
  have h := congrArg (coeff (m + 5)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 5 - 1 = m + 4 from by omega, show m + 5 - 2 = m + 3 from by omega, show m + 5 - 3 = m + 2 from by omega] at h
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

theorem hs1 : coeff 1 S = (-3 : ℚ) := by
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

theorem hs3 : coeff 3 S = (-6 : ℚ) := by
  have h := congrArg (coeff 2) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2] at h ⊢ <;> linarith

theorem hs4 : coeff 4 S = (-20 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hs5 : coeff 5 S = (-72 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hs6 : coeff 6 S = (-274 : ℚ) := by
  have h := congrArg (coeff 5) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hs7 : coeff 7 S = (-1086 : ℚ) := by
  have h := congrArg (coeff 6) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at h ⊢ <;> linarith

theorem hs8 : coeff 8 S = (-4438 : ℚ) := by
  have h := congrArg (coeff 7) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h ⊢ <;> linarith

theorem hs9 : coeff 9 S = (-18570 : ℚ) := by
  have h := congrArg (coeff 8) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at h ⊢ <;> linarith

theorem hs10 : coeff 10 S = (-79174 : ℚ) := by
  have h := congrArg (coeff 9) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (0 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (0 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (0 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (3 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (11 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (48 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (224 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (1071 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (5169 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem hf9 : coeff 9 F = (25053 : ℚ) := by
  have h := congrArg (coeff 9) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf0c] at h ⊢ <;> linarith

theorem hf10 : coeff 10 F = (121711 : ℚ) := by
  have h := congrArg (coeff 10) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (0 : ℚ) := by rw [a_eq]; exact hf2

theorem ha1 : a 1 = (3 : ℚ) := by rw [a_eq]; exact hf3

theorem ha2 : a 2 = (11 : ℚ) := by rw [a_eq]; exact hf4

theorem ha3 : a 3 = (48 : ℚ) := by rw [a_eq]; exact hf5

theorem ha4 : a 4 = (224 : ℚ) := by rw [a_eq]; exact hf6

theorem ha5 : a 5 = (1071 : ℚ) := by rw [a_eq]; exact hf7

theorem ha6 : a 6 = (5169 : ℚ) := by rw [a_eq]; exact hf8

theorem ha7 : a 7 = (25053 : ℚ) := by rw [a_eq]; exact hf9

theorem ha8 : a 8 = (121711 : ℚ) := by rw [a_eq]; exact hf10

noncomputable def Mv (n : ℕ) : ℚ := (-478 * (n : ℚ) ^ 2 + 1548 * (n : ℚ) + 5008) * a n
      + (4620 * (n : ℚ) ^ 2 - 20937 * (n : ℚ) - 12138) * a (n - 1)
      + (-12902 * (n : ℚ) ^ 2 + 76676 * (n : ℚ) - 77157) * a (n - 2)
      + (8760 * (n : ℚ) ^ 2 - 59835 * (n : ℚ) + 100665) * a (n - 3)

theorem base4 : Mv 4 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

theorem base5 : Mv 5 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

theorem base6 : Mv 6 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

theorem base7 : Mv 7 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

theorem base8 : Mv 8 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

theorem certQ (k : ℕ) : ((-6517425 / 14943236 : ℚ) + (9443410 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-5 / 239 : ℚ) * ((k : ℚ) + 7) ^ 2) * Mv (k + 7) + ((8641827 / 13875862 : ℚ) + (-12551310 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 1 + (6 / 239 : ℚ) * ((k : ℚ) + 7) ^ 2) * Mv (k + 8) + ((-25312845 / 194262068 : ℚ) + (2295088 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-1 / 239 : ℚ) * ((k : ℚ) + 7) ^ 2) * Mv (k + 9) = 0 := by
  unfold Mv
  rw [show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega, show k + 7 - 3 = k + 4 from by omega, show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 9 - 1 = k + 8 from by omega, show k + 9 - 2 = k + 7 from by omega, show k + 9 - 3 = k + 6 from by omega]
  simp only [a_eq]
  have r1_49 := rel1 (k + 3)
  have r1_50 := rel1 (k + 4)
  have r1_51 := rel1 (k + 5)
  have r1_52 := rel1 (k + 6)
  have r2_47 := rel2 (k + 4)
  have r2_48 := rel2 (k + 5)
  have r2_49 := rel2 (k + 6)
  have r2_50 := rel2 (k + 7)
  have r2_51 := rel2 (k + 8)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_49 r1_50 r1_51 r1_52 r2_47 r2_48 r2_49 r2_50 r2_51 ⊢
  push_cast at r1_49 r1_50 r1_51 r1_52 r2_47 r2_48 r2_49 r2_50 r2_51 ⊢
  linear_combination ((-131215317525 / 29886472 : ℚ) + (1774419018795 / 388524136 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-170574935415 / 97131034 : ℚ) * ((k : ℚ) + 7) ^ 2 + (28703505825 / 97131034 : ℚ) * ((k : ℚ) + 7) ^ 3 + (-4380 / 239 : ℚ) * ((k : ℚ) + 7) ^ 4) * r1_49 + ((460424907099 / 388524136 : ℚ) + (-22763072301 / 6937931 : ℚ) * ((k : ℚ) + 7) ^ 1 + (12535717069 / 6698692 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-18906249228 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 3 + (6451 / 239 : ℚ) * ((k : ℚ) + 7) ^ 4) * r1_50 + ((86792941773 / 48565517 : ℚ) + (-101174902659 / 388524136 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-745825785 / 1982266 : ℚ) * ((k : ℚ) + 7) ^ 2 + (151757955 / 1261442 : ℚ) * ((k : ℚ) + 7) ^ 3 + (-2310 / 239 : ℚ) * ((k : ℚ) + 7) ^ 4) * r1_51 + ((-19592142030 / 48565517 : ℚ) + (16514653791 / 97131034 : ℚ) * ((k : ℚ) + 7) ^ 1 + (1862479939 / 194262068 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-511543086 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 3 + (1 : ℚ) * ((k : ℚ) + 7) ^ 4) * r1_52 + ((-131215317525 / 59772944 : ℚ) + (10766243835 / 6937931 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-70089992955 / 194262068 : ℚ) * ((k : ℚ) + 7) ^ 2 + (6570 / 239 : ℚ) * ((k : ℚ) + 7) ^ 3) * r2_47 + ((329569668189 / 55503448 : ℚ) + (-226752457203 / 55503448 : ℚ) * ((k : ℚ) + 7) ^ 1 + (88860474693 / 97131034 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-31617 / 478 : ℚ) * ((k : ℚ) + 7) ^ 3) * r2_48 + ((-3212700973569 / 777048272 : ℚ) + (136416599742 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-119725486315 / 194262068 : ℚ) * ((k : ℚ) + 7) ^ 2 + (10394 / 239 : ℚ) * ((k : ℚ) + 7) ^ 3) * r2_49 + ((106842316257 / 97131034 : ℚ) + (-288142871229 / 388524136 : ℚ) * ((k : ℚ) + 7) ^ 1 + (7799647860 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-5337 / 478 : ℚ) * ((k : ℚ) + 7) ^ 3) * r2_50 + ((-9796071015 / 97131034 : ℚ) + (13155362403 / 194262068 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-705805154 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 2 + (1 : ℚ) * ((k : ℚ) + 7) ^ 3) * r2_51

theorem Mv_zero : ∀ n : ℕ, 4 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 9
    · interval_cases n
      · exact base4
      · exact base5
      · exact base6
      · exact base7
      · exact base8
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 7) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 8) = 0 := ih _ (by omega) (by omega)
      have hq : ((-25312845 / 194262068 : ℚ) + (2295088 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-1 / 239 : ℚ) * ((k : ℚ) + 7) ^ 2) ≠ 0 := by
        have e : ((-25312845 / 194262068 : ℚ) + (2295088 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-1 / 239 : ℚ) * ((k : ℚ) + 7) ^ 2) = -((878169 / 194262068 : ℚ) + (549754 / 48565517 : ℚ) * (k : ℚ) ^ 1 + (1 / 239 : ℚ) * (k : ℚ) ^ 2) := by ring
        rw [e, neg_ne_zero]
        positivity
      have hm : ((-25312845 / 194262068 : ℚ) + (2295088 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-1 / 239 : ℚ) * ((k : ℚ) + 7) ^ 2) * Mv (k + 9) = 0 := by linear_combination hc - ((-6517425 / 14943236 : ℚ) + (9443410 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-5 / 239 : ℚ) * ((k : ℚ) + 7) ^ 2) * h0 - ((8641827 / 13875862 : ℚ) + (-12551310 / 48565517 : ℚ) * ((k : ℚ) + 7) ^ 1 + (6 / 239 : ℚ) * ((k : ℚ) + 7) ^ 2) * h1
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 4 ≤ n → (-478 * (n : ℚ) ^ 2 + 1548 * (n : ℚ) + 5008) * a n
      + (4620 * (n : ℚ) ^ 2 - 20937 * (n : ℚ) - 12138) * a (n - 1)
      + (-12902 * (n : ℚ) ^ 2 + 76676 * (n : ℚ) - 77157) * a (n - 2)
      + (8760 * (n : ℚ) ^ 2 - 59835 * (n : ℚ) + 100665) * a (n - 3) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a126180

theorem OMA.solution : type_of% @OMA.S_oeis_a126180.main := OMA.P_oeis_a126180.main'
