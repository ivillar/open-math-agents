import OMAStatements.S_oeis_a126932
import Mathlib

-- Problem: A126932, conjectured recurrence for the g.f. (sqrt(1-2x-3x^2) + 3(1-3x))/(2(2-13x+21x^2)).
-- Upstream: formal-conjectures statements/oeis-a126932.lean (declaration OMA.S_oeis_a126932.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: the product of the two binomial series equals S = sqrt(1 - 2x - 3x^2) (both square to it,
-- with constant term 1). With 2 R S' = R' S and C F = A + B S, the recurrence follows from an explicit
-- polynomial certificate (and an induction from exact initial values when needed).

namespace OMA.P_oeis_a126932

open OMA.S_oeis_a126932 PowerSeries

noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2

noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

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

theorem hRC : R = C (1 : ℚ) + C (-2 : ℚ) * X ^ 1 + C (-3 : ℚ) * X ^ 2 := by
  simp only [R, map_one, map_neg, map_ofNat] <;> ring

theorem hDR : d⁄dX ℚ R = C (-2 : ℚ) + C (-6 : ℚ) * X ^ 1 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  try push_cast
  try ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-4 : ℚ) * X ^ 1 * d⁄dX ℚ S + C (-6 : ℚ) * X ^ 2 * d⁄dX ℚ S - (C (-2 : ℚ) * S + C (-6 : ℚ) * X ^ 1 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (-4 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (-6 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-2 : ℚ) * coeff (m + 2) S + (-6 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 2)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((3 - 9 * X + S) * (4 - 26 * X + 42 * X ^ 2 : PowerSeries ℚ)⁻¹)

theorem S_const0 : constantCoeff S = 1 := by
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

theorem root_sq : root ^ 2 = R := by
  have h : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = 1 + X := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    have h12 : (1 / 2 + 1 / 2 : ℚ) = ((1 : ℕ) : ℚ) := by norm_num
    rw [h12, PowerSeries.binomialSeries_nat, pow_one]
  unfold root R
  rw [mul_pow, ← map_pow, h, map_add, map_one, rescale_X]
  simp only [map_neg, map_ofNat]
  ring

theorem root_const : constantCoeff root = 1 := by
  unfold root
  rw [map_mul, ← coeff_zero_eq_constantCoeff_apply (rescale _ _), coeff_rescale]
  simp

theorem hroot : root = S := by
  have h : (root - S) * (root + S) = 0 := by
    linear_combination root_sq - S_sq
  rcases mul_eq_zero.mp h with h1 | h1
  · exact sub_eq_zero.mp h1
  · exfalso
    have h2 := congrArg constantCoeff h1
    rw [map_add, root_const, S_const0, map_zero] at h2
    norm_num at h2

theorem a_eq (n : ℕ) : a n = coeff n F := by
  unfold a generatingFunction F
  rw [hroot, show (S + C (3 : ℚ) * (1 - C (3 : ℚ) * X) : ℚ⟦X⟧) = 3 - 9 * X + S from by
      simp only [map_ofNat]; ring,
    show (C (2 : ℚ) * (C (2 : ℚ) - C (13 : ℚ) * X + C (21 : ℚ) * X ^ 2) : ℚ⟦X⟧) = 4 - 26 * X + 42 * X ^ 2 from by
      simp only [map_ofNat]; ring]

theorem hF : F * (4 - 26 * X + 42 * X ^ 2 : ℚ⟦X⟧) = 3 - 9 * X + S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (4 - 26 * X + 42 * X ^ 2 : ℚ⟦X⟧) = C (4 : ℚ) + C (-26 : ℚ) * X ^ 1 + C (42 : ℚ) * X ^ 2 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (4 : ℚ) * F + C (-26 : ℚ) * X ^ 1 * F + C (42 : ℚ) * X ^ 2 * F - (C (1 : ℚ) * S) - (C (3 : ℚ) + C (-9 : ℚ) * X ^ 1) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (4 : ℚ) * coeff (m + 2) F + (-26 : ℚ) * coeff (m + 1) F + (42 : ℚ) * coeff (m) F - ((1 : ℚ) * coeff (m + 2) S) = 0 := by
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

theorem hs1 : coeff 1 S = (-1 : ℚ) := by
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

theorem hs3 : coeff 3 S = (-2 : ℚ) := by
  have h := congrArg (coeff 2) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (1 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (1 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (4 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (15 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (55 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (1 : ℚ) := by rw [a_eq]; exact hf0

theorem ha1 : a 1 = (4 : ℚ) := by rw [a_eq]; exact hf1

theorem ha2 : a 2 = (15 : ℚ) := by rw [a_eq]; exact hf2

theorem ha3 : a 3 = (55 : ℚ) := by rw [a_eq]; exact hf3

noncomputable def Mv (n : ℕ) : ℚ := (2 * (n : ℚ)) * a n + (-11 * (n : ℚ)) * a (n - 1) + (8 * (n : ℚ) + 12) * a (n - 2)
      + (21 * (n : ℚ) - 42) * a (n - 3)

theorem base3 : Mv 3 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3]

theorem certQ (k : ℕ) : ((-12 : ℚ)) * Mv (k + 3) + ((4 : ℚ)) * Mv (k + 4) = 0 := by
  unfold Mv
  rw [show k + 3 - 1 = k + 2 from by omega, show k + 3 - 2 = k + 1 from by omega, show k + 3 - 3 = k from by omega, show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 4 - 3 = k + 1 from by omega]
  simp only [a_eq]
  have r1_49 := rel1 (k)
  have r1_50 := rel1 (k + 1)
  have r1_51 := rel1 (k + 2)
  have r2_50 := rel2 (k + 1)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_49 r1_50 r1_51 r2_50 ⊢
  push_cast at r1_49 r1_50 r1_51 r2_50 ⊢
  linear_combination ((12 : ℚ) + (-6 : ℚ) * ((k : ℚ) + 3) ^ 1) * r1_49 + ((2 : ℚ) + (-4 : ℚ) * ((k : ℚ) + 3) ^ 1) * r1_50 + ((2 : ℚ) + (2 : ℚ) * ((k : ℚ) + 3) ^ 1) * r1_51 + ((1 : ℚ)) * r2_50

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
      have hq : ((4 : ℚ)) ≠ 0 := by
        have e : ((4 : ℚ)) = (4 : ℚ) := by ring
        rw [e]
        positivity
      have hm : ((4 : ℚ)) * Mv (k + 4) = 0 := by linear_combination hc - ((-12 : ℚ)) * h0
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem mainQ : ∀ n : ℕ, 3 ≤ n → (2 * (n : ℚ)) * a n + (-11 * (n : ℚ)) * a (n - 1) + (8 * (n : ℚ) + 12) * a (n - 2)
      + (21 * (n : ℚ) - 42) * a (n - 3) = 0 := fun n hn => Mv_zero n hn

theorem main' : ∀ n : ℕ, 3 ≤ n →
    2 * (n : ℚ) * a n - 11 * (n : ℚ) * a (n - 1) +
      4 * (2 * (n : ℚ) + 3) * a (n - 2) +
      21 * ((n : ℚ) - 2) * a (n - 3) = 0 := by
  intro n hn
  have h := mainQ n hn
  linear_combination h

end OMA.P_oeis_a126932

theorem OMA.solution : type_of% @OMA.S_oeis_a126932.main := OMA.P_oeis_a126932.main'
