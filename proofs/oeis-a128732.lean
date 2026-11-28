import OMAStatements.S_oeis_a128732
import Mathlib

-- Problem: A128732: Number DL's in all skew Dyck paths of semilength n.
-- Upstream: formal-conjectures statements/oeis-a128732.lean (declaration OMA.S_oeis_a128732.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a128732

open OMA.S_oeis_a128732 PowerSeries

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

noncomputable def F : ℚ⟦X⟧ := ((-1 + 5 * X + (1 - 2 * X) * S) * (4 - 22 * X + 10 * X ^ 2 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff n F := rfl

theorem hF : F * (4 - 22 * X + 10 * X ^ 2 : ℚ⟦X⟧) = -1 + 5 * X + (1 - 2 * X) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (4 - 22 * X + 10 * X ^ 2 : ℚ⟦X⟧) = C (4 : ℚ) + C (-22 : ℚ) * X ^ 1 + C (10 : ℚ) * X ^ 2 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (4 : ℚ) * F + C (-22 : ℚ) * X ^ 1 * F + C (10 : ℚ) * X ^ 2 * F - (C (1 : ℚ) * S + C (-2 : ℚ) * X ^ 1 * S) - (C (-1 : ℚ) + C (5 : ℚ) * X ^ 1) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (4 : ℚ) * coeff (m + 2) F + (-22 : ℚ) * coeff (m + 1) F + (10 : ℚ) * coeff (m) F - ((1 : ℚ) * coeff (m + 2) S + (-2 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 2)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at h
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

theorem hf0 : coeff 0 F = (0 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (0 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (1 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (5 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (0 : ℚ) := by rw [a_eq]; exact hf0

theorem ha1 : a 1 = (0 : ℚ) := by rw [a_eq]; exact hf1

theorem ha2 : a 2 = (1 : ℚ) := by rw [a_eq]; exact hf2

theorem ha3 : a 3 = (5 : ℚ) := by rw [a_eq]; exact hf3

noncomputable def Mv (n : ℕ) : ℚ := (6 * (n : ℚ) ^ 2 - 2 * (n : ℚ)) * a n + (-39 * (n : ℚ) ^ 2 + 37 * (n : ℚ)) * a (n - 1)
      + (48 * (n : ℚ) ^ 2 - 88 * (n : ℚ) - 60) * a (n - 2)
      + (-15 * (n : ℚ) ^ 2 + 35 * (n : ℚ) + 30) * a (n - 3)

theorem base3 : Mv 3 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3]

theorem certQ (k : ℕ) : ((-20 / 3 : ℚ) * ((k : ℚ) + 3) ^ 1) * Mv (k + 3) + ((-4 / 3 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 3) ^ 1) * Mv (k + 4) = 0 := by
  unfold Mv
  rw [show k + 3 - 1 = k + 2 from by omega, show k + 3 - 2 = k + 1 from by omega, show k + 3 - 3 = k from by omega, show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 4 - 3 = k + 1 from by omega]
  simp only [a_eq]
  have r1_49 := rel1 (k)
  have r1_50 := rel1 (k + 1)
  have r1_51 := rel1 (k + 2)
  have r2_49 := rel2 (k)
  have r2_50 := rel2 (k + 1)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_49 r1_50 r1_51 r2_49 r2_50 ⊢
  push_cast at r1_49 r1_50 r1_51 r2_49 r2_50 ⊢
  linear_combination ((-20 : ℚ) * ((k : ℚ) + 3) ^ 1 + (-70 / 3 : ℚ) * ((k : ℚ) + 3) ^ 2 + (10 : ℚ) * ((k : ℚ) + 3) ^ 3) * r1_49 + ((-20 / 3 : ℚ) + (2 : ℚ) * ((k : ℚ) + 3) ^ 1 + (10 : ℚ) * ((k : ℚ) + 3) ^ 2 + (-12 : ℚ) * ((k : ℚ) + 3) ^ 3) * r1_50 + ((-4 / 3 : ℚ) + (-2 : ℚ) * ((k : ℚ) + 3) ^ 1 + (4 / 3 : ℚ) * ((k : ℚ) + 3) ^ 2 + (2 : ℚ) * ((k : ℚ) + 3) ^ 3) * r1_51 + ((-4 / 3 : ℚ) * ((k : ℚ) + 3) ^ 1 + (-2 : ℚ) * ((k : ℚ) + 3) ^ 2) * r2_49 + ((-2 / 3 : ℚ) + (-1 / 3 : ℚ) * ((k : ℚ) + 3) ^ 1 + (1 : ℚ) * ((k : ℚ) + 3) ^ 2) * r2_50

theorem Mv_zero : ∀ n : ℕ, 3 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 4
    · interval_cases n
      · exact base3
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 3) = 0 := ih _ (by omega) (by omega)
      have hq : ((-4 / 3 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 3) ^ 1) ≠ 0 := by
        have e : ((-4 / 3 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 3) ^ 1) = (8 / 3 : ℚ) + (4 / 3 : ℚ) * (k : ℚ) ^ 1 := by ring
        rw [e]
        positivity
      have hm : ((-4 / 3 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 3) ^ 1) * Mv (k + 4) = 0 := by linear_combination hc - ((-20 / 3 : ℚ) * ((k : ℚ) + 3) ^ 1) * h0
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 3 ≤ n → (6 * (n : ℚ) ^ 2 - 2 * (n : ℚ)) * a n + (-39 * (n : ℚ) ^ 2 + 37 * (n : ℚ)) * a (n - 1)
      + (48 * (n : ℚ) ^ 2 - 88 * (n : ℚ) - 60) * a (n - 2)
      + (-15 * (n : ℚ) ^ 2 + 35 * (n : ℚ) + 30) * a (n - 3) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a128732

theorem OMA.solution : type_of% @OMA.S_oeis_a128732.main := OMA.P_oeis_a128732.main'
