import OMAStatements.S_oeis_a124431
import Mathlib

-- Problem: A124431: a(n) = Sum_{k=0..n} 2^k*C([(n+k)/2],k)*C([(n+k+1)/2],k) where [x]=floor(x).
-- Upstream: formal-conjectures statements/oeis-a124431.lean (declaration OMA.S_oeis_a124431.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a124431

open OMA.S_oeis_a124431 PowerSeries

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

theorem hRC : R = C (1 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (2 : ℚ) * X ^ 2 + C (-4 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-4 : ℚ) + C (4 : ℚ) * X ^ 1 + C (-12 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-8 : ℚ) * X ^ 1 * d⁄dX ℚ S + C (4 : ℚ) * X ^ 2 * d⁄dX ℚ S + C (-8 : ℚ) * X ^ 3 * d⁄dX ℚ S + C (2 : ℚ) * X ^ 4 * d⁄dX ℚ S - (C (-4 : ℚ) * S + C (4 : ℚ) * X ^ 1 * S + C (-12 : ℚ) * X ^ 2 * S + C (4 : ℚ) * X ^ 3 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 5) S * ((m : ℚ) + 5)) + (-8 : ℚ) * (coeff (m + 4) S * ((m : ℚ) + 4)) + (4 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (-8 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (2 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-4 : ℚ) * coeff (m + 4) S + (4 : ℚ) * coeff (m + 3) S + (-12 : ℚ) * coeff (m + 2) S + (4 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 4)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 4 - 1 = m + 3 from by omega, show m + 4 - 2 = m + 2 from by omega, show m + 4 - 3 = m + 1 from by omega, show m + 4 - 4 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((-1 + 4 * X - X ^ 2 + S) * (2 - 8 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff (n + 1) F := rfl

theorem hF : F * (2 - 8 * X + 2 * X ^ 2 : ℚ⟦X⟧) = -1 + 4 * X - X ^ 2 + S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 - 8 * X + 2 * X ^ 2 : ℚ⟦X⟧) = C (2 : ℚ) + C (-8 : ℚ) * X ^ 1 + C (2 : ℚ) * X ^ 2 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (-8 : ℚ) * X ^ 1 * F + C (2 : ℚ) * X ^ 2 * F - (C (1 : ℚ) * S) - (C (-1 : ℚ) + C (4 : ℚ) * X ^ 1 + C (-1 : ℚ) * X ^ 2) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 3) F + (-8 : ℚ) * coeff (m + 2) F + (2 : ℚ) * coeff (m + 1) F - ((1 : ℚ) * coeff (m + 3) S) = 0 := by
  have h := congrArg (coeff (m + 3)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega] at h
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

theorem hs2 : coeff 2 S = (-1 : ℚ) := by
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

theorem hs4 : coeff 4 S = (-8 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hs5 : coeff 5 S = (-20 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hs6 : coeff 6 S = (-56 : ℚ) := by
  have h := congrArg (coeff 5) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (0 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (1 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (3 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (9 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (29 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (97 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (331 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (1 : ℚ) := by rw [a_eq]; exact hf1

theorem ha1 : a 1 = (3 : ℚ) := by rw [a_eq]; exact hf2

theorem ha2 : a 2 = (9 : ℚ) := by rw [a_eq]; exact hf3

theorem ha3 : a 3 = (29 : ℚ) := by rw [a_eq]; exact hf4

theorem ha4 : a 4 = (97 : ℚ) := by rw [a_eq]; exact hf5

theorem ha5 : a 5 = (331 : ℚ) := by rw [a_eq]; exact hf6

noncomputable def Mv (n : ℕ) : ℚ := ((n : ℚ) + 1) * a n + (-4 * (n : ℚ) - 2) * a (n - 1) + (2 * (n : ℚ) - 2) * a (n - 2)
      + (-4 * (n : ℚ) + 10) * a (n - 3) + ((n : ℚ) - 3) * a (n - 4)

theorem base4 : Mv 4 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5]

theorem base5 : Mv 5 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5]

theorem certQ (k : ℕ) : ((4 : ℚ)) * Mv (k + 4) + ((-16 : ℚ)) * Mv (k + 5) + ((4 : ℚ)) * Mv (k + 6) = 0 := by
  unfold Mv
  rw [show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 4 - 3 = k + 1 from by omega, show k + 4 - 4 = k from by omega, show k + 5 - 1 = k + 4 from by omega, show k + 5 - 2 = k + 3 from by omega, show k + 5 - 3 = k + 2 from by omega, show k + 5 - 4 = k + 1 from by omega, show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega, show k + 6 - 3 = k + 3 from by omega, show k + 6 - 4 = k + 2 from by omega]
  simp only [a_eq]
  have r1_48 := rel1 (k)
  have r1_49 := rel1 (k + 1)
  have r1_50 := rel1 (k + 2)
  have r1_51 := rel1 (k + 3)
  have r1_52 := rel1 (k + 4)
  have r2_51 := rel2 (k + 2)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_48 r1_49 r1_50 r1_51 r1_52 r2_51 ⊢
  push_cast at r1_48 r1_49 r1_50 r1_51 r1_52 r2_51 ⊢
  linear_combination ((-6 : ℚ) + (2 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_48 + ((12 : ℚ) + (-8 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_49 + ((4 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_50 + ((-12 : ℚ) + (-8 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_51 + ((6 : ℚ) + (2 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_52 + ((1 : ℚ)) * r2_51

theorem Mv_zero : ∀ n : ℕ, 4 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 6
    · interval_cases n
      · exact base4
      · exact base5
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 4) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 5) = 0 := ih _ (by omega) (by omega)
      have hq : ((4 : ℚ)) ≠ 0 := by
        have e : ((4 : ℚ)) = (4 : ℚ) := by ring
        rw [e]
        positivity
      have hm : ((4 : ℚ)) * Mv (k + 6) = 0 := by linear_combination hc - ((4 : ℚ)) * h0 - ((-16 : ℚ)) * h1
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 4 ≤ n → ((n : ℚ) + 1) * a n + (-4 * (n : ℚ) - 2) * a (n - 1) + (2 * (n : ℚ) - 2) * a (n - 2)
      + (-4 * (n : ℚ) + 10) * a (n - 3) + ((n : ℚ) - 3) * a (n - 4) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a124431

theorem OMA.solution : type_of% @OMA.S_oeis_a124431.main := OMA.P_oeis_a124431.main'
