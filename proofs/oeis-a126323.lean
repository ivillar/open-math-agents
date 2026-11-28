import OMAStatements.S_oeis_a126323
import Mathlib

-- Problem: A126323: Number of branches of length 1 in all hex trees with n edges.
-- Upstream: formal-conjectures statements/oeis-a126323.lean (declaration OMA.S_oeis_a126323.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a126323

open OMA.S_oeis_a126323 PowerSeries

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

noncomputable def F : ℚ⟦X⟧ := ((-2 + 27 * X - 136 * X ^ 2 + 318 * X ^ 3 - 342 * X ^ 4 + 135 * X ^ 5 + (2 - 21 * X + 77 * X ^ 2 - 111 * X ^ 3 + 45 * X ^ 4) * S) * (2 - 12 * X + 10 * X ^ 2 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff (n + 2) F := rfl

theorem hF : F * (2 - 12 * X + 10 * X ^ 2 : ℚ⟦X⟧) = -2 + 27 * X - 136 * X ^ 2 + 318 * X ^ 3 - 342 * X ^ 4 + 135 * X ^ 5 + (2 - 21 * X + 77 * X ^ 2 - 111 * X ^ 3 + 45 * X ^ 4) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 - 12 * X + 10 * X ^ 2 : ℚ⟦X⟧) = C (2 : ℚ) + C (-12 : ℚ) * X ^ 1 + C (10 : ℚ) * X ^ 2 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (-12 : ℚ) * X ^ 1 * F + C (10 : ℚ) * X ^ 2 * F - (C (2 : ℚ) * S + C (-21 : ℚ) * X ^ 1 * S + C (77 : ℚ) * X ^ 2 * S + C (-111 : ℚ) * X ^ 3 * S + C (45 : ℚ) * X ^ 4 * S) - (C (-2 : ℚ) + C (27 : ℚ) * X ^ 1 + C (-136 : ℚ) * X ^ 2 + C (318 : ℚ) * X ^ 3 + C (-342 : ℚ) * X ^ 4 + C (135 : ℚ) * X ^ 5) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 6) F + (-12 : ℚ) * coeff (m + 5) F + (10 : ℚ) * coeff (m + 4) F - ((2 : ℚ) * coeff (m + 6) S + (-21 : ℚ) * coeff (m + 5) S + (77 : ℚ) * coeff (m + 4) S + (-111 : ℚ) * coeff (m + 3) S + (45 : ℚ) * coeff (m + 2) S) = 0 := by
  have h := congrArg (coeff (m + 6)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 6 - 1 = m + 5 from by omega, show m + 6 - 2 = m + 4 from by omega, show m + 6 - 3 = m + 3 from by omega, show m + 6 - 4 = m + 2 from by omega] at h
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

theorem hf4 : coeff 4 F = (2 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (15 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (80 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (399 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (1956 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem hf9 : coeff 9 F = (9546 : ℚ) := by
  have h := congrArg (coeff 9) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf0c] at h ⊢ <;> linarith

theorem hf10 : coeff 10 F = (46552 : ℚ) := by
  have h := congrArg (coeff 10) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (0 : ℚ) := by rw [a_eq]; exact hf2

theorem ha1 : a 1 = (3 : ℚ) := by rw [a_eq]; exact hf3

theorem ha2 : a 2 = (2 : ℚ) := by rw [a_eq]; exact hf4

theorem ha3 : a 3 = (15 : ℚ) := by rw [a_eq]; exact hf5

theorem ha4 : a 4 = (80 : ℚ) := by rw [a_eq]; exact hf6

theorem ha5 : a 5 = (399 : ℚ) := by rw [a_eq]; exact hf7

theorem ha6 : a 6 = (1956 : ℚ) := by rw [a_eq]; exact hf8

theorem ha7 : a 7 = (9546 : ℚ) := by rw [a_eq]; exact hf9

theorem ha8 : a 8 = (46552 : ℚ) := by rw [a_eq]; exact hf10

noncomputable def Mv (n : ℕ) : ℚ := (-1176 * (n : ℚ) ^ 3 - 352487 * (n : ℚ) ^ 2 + 1394745 * (n : ℚ) + 4190030) * a n
      + (-1176 * (n : ℚ) ^ 3 + 3331731 * (n : ℚ) ^ 2 - 18691638 * (n : ℚ) - 3694740) * a (n - 1)
      + (43512 * (n : ℚ) ^ 3 - 9103273 * (n : ℚ) ^ 2 + 68264245 * (n : ℚ) - 103131090) * a (n - 2)
      + (-41160 * (n : ℚ) ^ 3 + 6142845 * (n : ℚ) ^ 2 - 52677180 * (n : ℚ) + 115057440) * a (n - 3)

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

theorem certQ (k : ℕ) : ((-281203802232888070522225 / 6558753824444162313704172 : ℚ) + (-1464439058378284800 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 1) * Mv (k + 5) + ((56785069048475834584885 / 546562818703680192808681 : ℚ) + (2902294844186599680 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 1) * Mv (k + 6) + ((-262479642232193431029359 / 3279376912222081156852086 : ℚ) + (-1666849380634846464 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 1) * Mv (k + 7) + ((11299670246529770664449 / 546562818703680192808681 : ℚ) + (228993594826531584 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 1) * Mv (k + 8) + ((-1 / 588 : ℚ)) * Mv (k + 9) = 0 := by
  unfold Mv
  rw [show k + 5 - 1 = k + 4 from by omega, show k + 5 - 2 = k + 3 from by omega, show k + 5 - 3 = k + 2 from by omega, show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega, show k + 6 - 3 = k + 3 from by omega, show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega, show k + 7 - 3 = k + 4 from by omega, show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 9 - 1 = k + 8 from by omega, show k + 9 - 2 = k + 7 from by omega, show k + 9 - 3 = k + 6 from by omega]
  simp only [a_eq]
  have r1_49 := rel1 (k)
  have r1_50 := rel1 (k + 1)
  have r1_51 := rel1 (k + 2)
  have r1_52 := rel1 (k + 3)
  have r1_53 := rel1 (k + 4)
  have r1_54 := rel1 (k + 5)
  have r2_46 := rel2 (k + 1)
  have r2_47 := rel2 (k + 2)
  have r2_48 := rel2 (k + 3)
  have r2_49 := rel2 (k + 4)
  have r2_50 := rel2 (k + 5)
  have r2_51 := rel2 (k + 6)
  have r2_52 := rel2 (k + 7)
  have r2_53 := rel2 (k + 8)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_49 r1_50 r1_51 r1_52 r1_53 r1_54 r2_46 r2_47 r2_48 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  push_cast at r1_49 r1_50 r1_51 r1_52 r1_53 r1_54 r2_46 r2_47 r2_48 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  linear_combination ((-269621580026519876673555596700 / 546562818703680192808681 : ℚ) + (245232474612659223372545667825 / 1093125637407360385617362 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-112135437922631863377639279875 / 4372502549629441542469448 : ℚ) * ((k : ℚ) + 5) ^ 2 + (1068844400873841004429975 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 3 + (6027631164285020236800 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 4) * r1_49 + ((1228012360579680385813874545545 / 2186251274814720771234724 : ℚ) + (-5788299703676450025117819351665 / 13117507648888324627408344 : ℚ) * ((k : ℚ) + 5) ^ 1 + (903047063409531684340010829635 / 13117507648888324627408344 : ℚ) * ((k : ℚ) + 5) ^ 2 + (-2488124601040959082783475 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 3 + (-11084755412345612820480 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 4) * r1_50 + ((33049968138748179507922892283 / 546562818703680192808681 : ℚ) + (139095980360118145785047049971 / 546562818703680192808681 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-142058049947140678278675262059 / 2186251274814720771234724 : ℚ) * ((k : ℚ) + 5) ^ 2 + (1499131721548384580195734 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 3 + (5154202682311307433984 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 4) * r1_51 + ((-230884762718883509038692417447 / 1093125637407360385617362 : ℚ) + (-209524324957211959767373247563 / 6558753824444162313704172 : ℚ) * ((k : ℚ) + 5) ^ 1 + (171865866116074500977073857911 / 6558753824444162313704172 : ℚ) * ((k : ℚ) + 5) ^ 2 + (6276892023567926448010 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 3 + (37569799507285721088 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 4) * r1_52 + ((29631056966755493741297662251 / 546562818703680192808681 : ℚ) + (-7524037357955873016653020807 / 1093125637407360385617362 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-20601023808103701381659468647 / 4372502549629441542469448 : ℚ) * ((k : ℚ) + 5) ^ 2 + (-99086107020034759082237 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 3 + (-134648233758000571392 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 4) * r1_53 + ((-675659 / 196 : ℚ) + (211657 / 168 : ℚ) * ((k : ℚ) + 5) ^ 1 + (366599 / 1176 : ℚ) * ((k : ℚ) + 5) ^ 2 + (1 : ℚ) * ((k : ℚ) + 5) ^ 3) * r1_54 + ((606648555059669722515500092575 / 1093125637407360385617362 : ℚ) + (-993795161394593565321910825275 / 8745005099258883084938896 : ℚ) * ((k : ℚ) + 5) ^ 1 + (9836594329778829768394575 / 22308686477701232359538 : ℚ) * ((k : ℚ) + 5) ^ 2 + (27124340239282591065600 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 3) * r2_46 + ((-9238241630285350616916868928655 / 4372502549629441542469448 : ℚ) + (247080166318878705101817544500 / 546562818703680192808681 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-17492866668210440552984175 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 2 + (-84238896991979873041920 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 3) * r2_47 + ((3195826387868278452176381424999 / 1093125637407360385617362 : ℚ) + (-5965476151642439384055499757357 / 8745005099258883084938896 : ℚ) * ((k : ℚ) + 5) ^ 1 + (41897209956804719529193351 / 22308686477701232359538 : ℚ) * ((k : ℚ) + 5) ^ 2 + (86135912674199475720192 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 3) * r2_48 + ((-8680286666828002081426070257179 / 4372502549629441542469448 : ℚ) + (6718020670661437526020078747015 / 13117507648888324627408344 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-9464873357999561217726265 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 2 + (-34842353188497142514688 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 3) * r2_49 + ((114232219053406755313406867593 / 156160805343908626516766 : ℚ) + (-1853757285935744507286641504453 / 8745005099258883084938896 : ℚ) * ((k : ℚ) + 5) ^ 1 + (1761764391007399095903525 / 22308686477701232359538 : ℚ) * ((k : ℚ) + 5) ^ 2 + (4109925065101517975040 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 3) * r2_50 + ((-644933355451462999957038292773 / 4372502549629441542469448 : ℚ) + (107837469107406635068814660527 / 2186251274814720771234724 : ℚ) * ((k : ℚ) + 5) ^ 1 + (523305491364402199459695 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 2 + (643486851418288292352 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 3) * r2_51 + ((16374342225753338582962990563 / 1093125637407360385617362 : ℚ) + (-52965724844288719519930583251 / 8745005099258883084938896 : ℚ) * ((k : ℚ) + 5) ^ 1 + (-297214820852145058068475 / 22308686477701232359538 : ℚ) * ((k : ℚ) + 5) ^ 2 + (-134648233758000571392 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 3) * r2_52 + ((-675659 / 1176 : ℚ) + (359543 / 1176 : ℚ) * ((k : ℚ) + 5) ^ 1 + (1 : ℚ) * ((k : ℚ) + 5) ^ 2) * r2_53

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
      have h0 : Mv (k + 5) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 6) = 0 := ih _ (by omega) (by omega)
      have h2 : Mv (k + 7) = 0 := ih _ (by omega) (by omega)
      have h3 : Mv (k + 8) = 0 := ih _ (by omega) (by omega)
      have hq : ((-1 / 588 : ℚ)) ≠ 0 := by
        have e : ((-1 / 588 : ℚ)) = -((1 / 588 : ℚ)) := by ring
        rw [e, neg_ne_zero]
        positivity
      have hm : ((-1 / 588 : ℚ)) * Mv (k + 9) = 0 := by linear_combination hc - ((-281203802232888070522225 / 6558753824444162313704172 : ℚ) + (-1464439058378284800 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 1) * h0 - ((56785069048475834584885 / 546562818703680192808681 : ℚ) + (2902294844186599680 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 1) * h1 - ((-262479642232193431029359 / 3279376912222081156852086 : ℚ) + (-1666849380634846464 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 1) * h2 - ((11299670246529770664449 / 546562818703680192808681 : ℚ) + (228993594826531584 / 11154343238850616179769 : ℚ) * ((k : ℚ) + 5) ^ 1) * h3
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 4 ≤ n → (-1176 * (n : ℚ) ^ 3 - 352487 * (n : ℚ) ^ 2 + 1394745 * (n : ℚ) + 4190030) * a n
      + (-1176 * (n : ℚ) ^ 3 + 3331731 * (n : ℚ) ^ 2 - 18691638 * (n : ℚ) - 3694740) * a (n - 1)
      + (43512 * (n : ℚ) ^ 3 - 9103273 * (n : ℚ) ^ 2 + 68264245 * (n : ℚ) - 103131090) * a (n - 2)
      + (-41160 * (n : ℚ) ^ 3 + 6142845 * (n : ℚ) ^ 2 - 52677180 * (n : ℚ) + 115057440) * a (n - 3) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a126323

theorem OMA.solution : type_of% @OMA.S_oeis_a126323.main := OMA.P_oeis_a126323.main'
