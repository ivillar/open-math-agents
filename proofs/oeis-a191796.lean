import OMAStatements.S_oeis_a191796
import Mathlib

-- Problem: A191796: Number of DUU's in all length n left factors of Dyck paths; here U=(1,1) and D=(1,-1).
-- Upstream: formal-conjectures statements/oeis-a191796.lean (declaration OMA.S_oeis_a191796.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a191796

open OMA.S_oeis_a191796 PowerSeries

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

theorem hRC : R = C (1 : ℚ) + C (-4 : ℚ) * X ^ 2 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-8 : ℚ) * X ^ 1 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-8 : ℚ) * X ^ 2 * d⁄dX ℚ S - (C (-8 : ℚ) * X ^ 1 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (-8 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-8 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 2)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((1 - 7 * X ^ 2 - X ^ 3 + 12 * X ^ 4 + 4 * X ^ 5 + (-1 + 5 * X ^ 2 + X ^ 3 - 4 * X ^ 4) * S) * (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff (n + 1) F := rfl

theorem hF : F * (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 : ℚ⟦X⟧) = 1 - 7 * X ^ 2 - X ^ 3 + 12 * X ^ 4 + 4 * X ^ 5 + (-1 + 5 * X ^ 2 + X ^ 3 - 4 * X ^ 4) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 : ℚ⟦X⟧) = C (2 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (-8 : ℚ) * X ^ 2 + C (16 : ℚ) * X ^ 3 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (-4 : ℚ) * X ^ 1 * F + C (-8 : ℚ) * X ^ 2 * F + C (16 : ℚ) * X ^ 3 * F - (C (-1 : ℚ) * S + C (5 : ℚ) * X ^ 2 * S + C (1 : ℚ) * X ^ 3 * S + C (-4 : ℚ) * X ^ 4 * S) - (C (1 : ℚ) + C (-7 : ℚ) * X ^ 2 + C (-1 : ℚ) * X ^ 3 + C (12 : ℚ) * X ^ 4 + C (4 : ℚ) * X ^ 5) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 6) F + (-4 : ℚ) * coeff (m + 5) F + (-8 : ℚ) * coeff (m + 4) F + (16 : ℚ) * coeff (m + 3) F - ((-1 : ℚ) * coeff (m + 6) S + (5 : ℚ) * coeff (m + 4) S + (1 : ℚ) * coeff (m + 3) S + (-4 : ℚ) * coeff (m + 2) S) = 0 := by
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

theorem hs1 : coeff 1 S = (0 : ℚ) := by
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

theorem hs3 : coeff 3 S = (0 : ℚ) := by
  have h := congrArg (coeff 2) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2] at h ⊢ <;> linarith

theorem hs4 : coeff 4 S = (-2 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hs5 : coeff 5 S = (0 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hs6 : coeff 6 S = (-4 : ℚ) := by
  have h := congrArg (coeff 5) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hs7 : coeff 7 S = (0 : ℚ) := by
  have h := congrArg (coeff 6) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at h ⊢ <;> linarith

theorem hs8 : coeff 8 S = (-10 : ℚ) := by
  have h := congrArg (coeff 7) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h ⊢ <;> linarith

theorem hs9 : coeff 9 S = (0 : ℚ) := by
  have h := congrArg (coeff 8) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at h ⊢ <;> linarith

theorem hs10 : coeff 10 S = (-28 : ℚ) := by
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

theorem hf3 : coeff 3 F = (0 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (0 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (1 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (3 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (9 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (21 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem hf9 : coeff 9 F = (52 : ℚ) := by
  have h := congrArg (coeff 9) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf0c] at h ⊢ <;> linarith

theorem hf10 : coeff 10 F = (113 : ℚ) := by
  have h := congrArg (coeff 10) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (0 : ℚ) := by rw [a_eq]; exact hf1

theorem ha1 : a 1 = (0 : ℚ) := by rw [a_eq]; exact hf2

theorem ha2 : a 2 = (0 : ℚ) := by rw [a_eq]; exact hf3

theorem ha3 : a 3 = (0 : ℚ) := by rw [a_eq]; exact hf4

theorem ha4 : a 4 = (1 : ℚ) := by rw [a_eq]; exact hf5

theorem ha5 : a 5 = (3 : ℚ) := by rw [a_eq]; exact hf6

theorem ha6 : a 6 = (9 : ℚ) := by rw [a_eq]; exact hf7

theorem ha7 : a 7 = (21 : ℚ) := by rw [a_eq]; exact hf8

theorem ha8 : a 8 = (52 : ℚ) := by rw [a_eq]; exact hf9

theorem ha9 : a 9 = (113 : ℚ) := by rw [a_eq]; exact hf10

noncomputable def Mv (n : ℕ) : ℚ := (-2527 * (n : ℚ) ^ 3 - 18490 * (n : ℚ) ^ 2 + 130597 * (n : ℚ) + 146560) * a n
      + (-2527 * (n : ℚ) ^ 3 + 68000 * (n : ℚ) ^ 2 - 231053 * (n : ℚ) - 293120) * a (n - 1)
      + (25270 * (n : ℚ) ^ 3 + 1812 * (n : ℚ) ^ 2 - 858790 * (n : ℚ) + 1492968) * a (n - 2)
      + (10108 * (n : ℚ) ^ 3 - 282108 * (n : ℚ) ^ 2 + 1266968 * (n : ℚ) - 1266096) * a (n - 3)
      + (-60648 * (n : ℚ) ^ 3 + 308808 * (n : ℚ) ^ 2 + 660096 * (n : ℚ) - 3439680) * a (n - 4)

theorem base5 : Mv 5 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem base6 : Mv 6 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem base7 : Mv 7 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem base8 : Mv 8 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem base9 : Mv 9 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]

theorem certQ (k : ℕ) : ((220582921496561143232 / 12106468531976659356117 : ℚ) + (9974424441916928 / 14372538819125436513 : ℚ) * ((k : ℚ) + 6) ^ 1) * Mv (k + 6) + ((21178131858036992 / 4790846273041812171 : ℚ) + (-1158052117454848 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 1) * Mv (k + 7) + ((-370192441663703764576 / 36319405595929978068351 : ℚ) + (-2493606110479232 / 14372538819125436513 : ℚ) * ((k : ℚ) + 6) ^ 1) * Mv (k + 8) + ((-2150861693988032 / 1596948757680604057 : ℚ) + (289513029363712 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 1) * Mv (k + 9) + ((4 / 2527 : ℚ)) * Mv (k + 10) = 0 := by
  unfold Mv
  rw [show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega, show k + 6 - 3 = k + 3 from by omega, show k + 6 - 4 = k + 2 from by omega, show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega, show k + 7 - 3 = k + 4 from by omega, show k + 7 - 4 = k + 3 from by omega, show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 8 - 4 = k + 4 from by omega, show k + 9 - 1 = k + 8 from by omega, show k + 9 - 2 = k + 7 from by omega, show k + 9 - 3 = k + 6 from by omega, show k + 9 - 4 = k + 5 from by omega, show k + 10 - 1 = k + 9 from by omega, show k + 10 - 2 = k + 8 from by omega, show k + 10 - 3 = k + 7 from by omega, show k + 10 - 4 = k + 6 from by omega]
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
  linear_combination ((-15806972154443571524005120 / 4035489510658886452039 : ℚ) + (7294152154593999163346432 / 12106468531976659356117 : ℚ) * ((k : ℚ) + 6) ^ 1 + (1534661644116821284207776 / 4035489510658886452039 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-5229488678387630560 / 93938162216506121 : ℚ) * ((k : ℚ) + 6) ^ 3 + (-12602685282362038528 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 4) * r1_49 + ((-16544188684943553429143616 / 4035489510658886452039 : ℚ) + (8192449356984904460728672 / 4035489510658886452039 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-2094146747852955625743584 / 36319405595929978068351 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-75428773674396422176 / 1596948757680604057 : ℚ) * ((k : ℚ) + 6) ^ 3 + (566104371275765504 / 14372538819125436513 : ℚ) * ((k : ℚ) + 6) ^ 4) * r1_50 + ((-2144697922893465441850240 / 4035489510658886452039 : ℚ) + (-1088883118833348159289160 / 4035489510658886452039 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-328738034019294922704536 / 12106468531976659356117 : ℚ) * ((k : ℚ) + 6) ^ 2 + (177982325088266041904 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 3 + (1537956723664903360 / 1596948757680604057 : ℚ) * ((k : ℚ) + 6) ^ 4) * r1_51 + ((-614380262212583043069744 / 576498501522698064577 : ℚ) + (-5407351714479805608092320 / 12106468531976659356117 : ℚ) * ((k : ℚ) + 6) ^ 1 + (6778177672160532463437608 / 36319405595929978068351 : ℚ) * ((k : ℚ) + 6) ^ 2 + (94756824347312872624 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 3 + (-141526092818941376 / 14372538819125436513 : ℚ) * ((k : ℚ) + 6) ^ 4) * r1_52 + ((-404735604574406017725784 / 4035489510658886452039 : ℚ) + (-312970752381603275345698 / 12106468531976659356117 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-256043151858239244431680 / 12106468531976659356117 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-26560981757066206178 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 3 + (-365799712601050112 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 4) * r1_53 + ((422760 / 2527 : ℚ) + (-277238 / 2527 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-97628 / 2527 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-2 : ℚ) * ((k : ℚ) + 6) ^ 3) * r1_54 + ((1580697215444357152400512 / 4035489510658886452039 : ℚ) + (12882536106306727947392 / 712145207763332903301 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-164858674504789675600 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-6301342641181019264 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_46 + ((1574055705791582568517792 / 4035489510658886452039 : ℚ) + (-97863792629093516031196 / 712145207763332903301 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-219379273894525876532 / 14372538819125436513 : ℚ) * ((k : ℚ) + 6) ^ 2 + (5009059166523647200 / 14372538819125436513 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_47 + ((-3361561204325421694673592 / 4035489510658886452039 : ℚ) + (-1896366683915314871969816 / 36319405595929978068351 : ℚ) * ((k : ℚ) + 6) ^ 1 + (90552325707885382108 / 1596948757680604057 : ℚ) * ((k : ℚ) + 6) ^ 2 + (25754070133625652224 / 14372538819125436513 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_48 + ((-4032180162129733890286244 / 4035489510658886452039 : ℚ) + (660530641269592844633221 / 4035489510658886452039 : ℚ) * ((k : ℚ) + 6) ^ 1 + (441776603664189179813 / 14372538819125436513 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-902514800948928608 / 14372538819125436513 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_49 + ((300220390348223385521106 / 4035489510658886452039 : ℚ) + (-51026380967215329855658 / 12106468531976659356117 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-34759209362572825564 / 1596948757680604057 : ℚ) * ((k : ℚ) + 6) ^ 2 + (-2489834941797880096 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_50 + ((1099348404766343113892516 / 4035489510658886452039 : ℚ) + (-196376941431203892316385 / 2136435623289998709903 : ℚ) * ((k : ℚ) + 6) ^ 1 + (-17413340497702573057 / 1596948757680604057 : ℚ) * ((k : ℚ) + 6) ^ 2 + (70763046409470688 / 14372538819125436513 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_51 + ((50591950571800752215723 / 4035489510658886452039 : ℚ) + (1177381118849845256420 / 12106468531976659356117 : ℚ) * ((k : ℚ) + 6) ^ 1 + (4182963817777000955 / 1596948757680604057 : ℚ) * ((k : ℚ) + 6) ^ 2 + (182899856300525056 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 3) * r2_52 + ((-42276 / 2527 : ℚ) + (36179 / 2527 : ℚ) * ((k : ℚ) + 6) ^ 1 + (1 : ℚ) * ((k : ℚ) + 6) ^ 2) * r2_53

theorem Mv_zero : ∀ n : ℕ, 5 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 10
    · interval_cases n
      · exact base5
      · exact base6
      · exact base7
      · exact base8
      · exact base9
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 6) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 7) = 0 := ih _ (by omega) (by omega)
      have h2 : Mv (k + 8) = 0 := ih _ (by omega) (by omega)
      have h3 : Mv (k + 9) = 0 := ih _ (by omega) (by omega)
      have hq : ((4 / 2527 : ℚ)) ≠ 0 := by
        have e : ((4 / 2527 : ℚ)) = (4 / 2527 : ℚ) := by ring
        rw [e]
        positivity
      have hm : ((4 / 2527 : ℚ)) * Mv (k + 10) = 0 := by linear_combination hc - ((220582921496561143232 / 12106468531976659356117 : ℚ) + (9974424441916928 / 14372538819125436513 : ℚ) * ((k : ℚ) + 6) ^ 1) * h0 - ((21178131858036992 / 4790846273041812171 : ℚ) + (-1158052117454848 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 1) * h1 - ((-370192441663703764576 / 36319405595929978068351 : ℚ) + (-2493606110479232 / 14372538819125436513 : ℚ) * ((k : ℚ) + 6) ^ 1) * h2 - ((-2150861693988032 / 1596948757680604057 : ℚ) + (289513029363712 / 4790846273041812171 : ℚ) * ((k : ℚ) + 6) ^ 1) * h3
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 5 ≤ n → (-2527 * (n : ℚ) ^ 3 - 18490 * (n : ℚ) ^ 2 + 130597 * (n : ℚ) + 146560) * a n
      + (-2527 * (n : ℚ) ^ 3 + 68000 * (n : ℚ) ^ 2 - 231053 * (n : ℚ) - 293120) * a (n - 1)
      + (25270 * (n : ℚ) ^ 3 + 1812 * (n : ℚ) ^ 2 - 858790 * (n : ℚ) + 1492968) * a (n - 2)
      + (10108 * (n : ℚ) ^ 3 - 282108 * (n : ℚ) ^ 2 + 1266968 * (n : ℚ) - 1266096) * a (n - 3)
      + (-60648 * (n : ℚ) ^ 3 + 308808 * (n : ℚ) ^ 2 + 660096 * (n : ℚ) - 3439680) * a (n - 4) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a191796

theorem OMA.solution : type_of% @OMA.S_oeis_a191796.main := OMA.P_oeis_a191796.main'
