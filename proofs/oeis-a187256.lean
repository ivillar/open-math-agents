import OMAStatements.S_oeis_a187256
import Mathlib

-- Problem: A187256, R. J. Mathar's conjectured recurrence for a(0) = 1, a(1) = 2,
-- a(n+2) = 2 a(n+1) + Sum_{k=0..n} a(k) a(n-k) - a(n).
-- Upstream: formal-conjectures statements/oeis-a187256.lean (declaration OMA.S_oeis_a187256.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof idea: the g.f. G satisfies x^2 G^2 - (1 - x)^2 G + 1 = 0 (Q1), so U = (1 - x)^2 - 2x^2 G
-- satisfies U^2 = R = (1 - x)^4 - 4x^2 and U(0) = 1, hence U = S = sqrt(R) (T_eq) and
-- x^2 G = ((1 - x)^2 - S)/2. With 2 R S' = R' S the recurrence follows from an explicit
-- polynomial certificate (and an induction from exact initial values when needed).

namespace OMA.P_oeis_a187256

open OMA.S_oeis_a187256 PowerSeries

noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4

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

noncomputable def F : ℚ⟦X⟧ := ((1 - 2 * X + X ^ 2 - S) * (2 : PowerSeries ℚ)⁻¹)

noncomputable def G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))

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

theorem Q1 : X ^ 2 * G ^ 2 - G + C (2 : ℚ) * (X * G) - X ^ 2 * G + 1 = 0 := by
  ext n
  rw [map_zero]
  rcases n with _ | _ | n
  · simp [G, a]
  · have e1 : coeff 1 (X ^ 2 * G ^ 2) = 0 := by simp [coeff_X_pow_mul']
    have e2 : coeff 1 (C (2 : ℚ) * (X * G)) = 2 * coeff 0 G := by rw [coeff_C_mul, coeff_succ_X_mul]
    have e3 : coeff 0 G = 1 := by simp [G, a]
    have e4 : coeff 1 G = 2 := by simp [G, a]
    have e5 : coeff 1 (X ^ 2 * G) = 0 := by simp [coeff_X_pow_mul']
    have e6 : coeff 1 (1 : ℚ⟦X⟧) = 0 := by simp [coeff_one]
    rw [map_add, map_sub, map_add, map_sub, e1, e2, e3, e4, e5, e6]
    ring
  · have h2 : coeff n (G ^ 2) = ∑ k ∈ Finset.range (n + 1), (a k : ℚ) * a (n - k) := by
      rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [G]
    have h3 : (a (n + 2) : ℚ) = 2 * (a (n + 1) : ℚ) + (∑ k ∈ Finset.range (n + 1), (a k : ℚ) * a (n - k)) - (a n : ℚ) := by
      rw [a]
      push_cast
      rw [Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ) * a (n - k))]
    have e1 : coeff (n + 2) (X ^ 2 * G ^ 2) = coeff n (G ^ 2) := by simp [coeff_X_pow_mul']
    have e2 : coeff (n + 2) (C (2 : ℚ) * (X * G)) = 2 * (a (n + 1) : ℚ) := by
      rw [coeff_C_mul, coeff_succ_X_mul]
      simp [G]
    have e3 : coeff (n + 2) G = (a (n + 2) : ℚ) := by simp [G]
    have e5 : coeff (n + 2) (X ^ 2 * G) = (a n : ℚ) := by simp [coeff_X_pow_mul', G]
    have e6 : coeff (n + 2) (1 : ℚ⟦X⟧) = 0 := by simp [coeff_one]
    rw [map_add, map_sub, map_add, map_sub, e1, e2, e3, e5, e6, h2, h3]
    ring

theorem T_eq : (1 - 2 * X + X ^ 2) - 2 * X ^ 2 * G = S := by
  have q := Q1
  simp only [map_ofNat] at q
  have hT : ((1 - 2 * X + X ^ 2) - 2 * X ^ 2 * G) ^ 2 = R := by
    unfold R
    linear_combination (4 * X ^ 2) * q
  have h : ((1 - 2 * X + X ^ 2) - 2 * X ^ 2 * G - S) * ((1 - 2 * X + X ^ 2) - 2 * X ^ 2 * G + S) = 0 := by
    linear_combination hT - S_sq
  rcases mul_eq_zero.mp h with h1 | h1
  · exact sub_eq_zero.mp h1
  · exfalso
    have h2 := congrArg constantCoeff h1
    norm_num [S_const0] at h2

theorem a_eq (n : ℕ) : (a n : ℚ) = coeff (n + 2) F := by
  have hF2 : F = X ^ 2 * G := by
    unfold F
    have e : 1 - 2 * X + X ^ 2 - S = X ^ 2 * G * 2 := by
      rw [← T_eq]
      ring
    rw [e, mul_assoc, PowerSeries.mul_inv_cancel _ (by
      rw [show (2 : ℚ⟦X⟧) = C (2 : ℚ) from by simp only [map_ofNat]]
      simp), mul_one]
  rw [hF2, coeff_X_pow_mul]
  simp [G]

theorem hF : F * (2 : ℚ⟦X⟧) = 1 - 2 * X + X ^ 2 - S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 : ℚ⟦X⟧) = C (2 : ℚ) from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F - (C (-1 : ℚ) * S) - (C (1 : ℚ) + C (-2 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 2) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 3) F - ((-1 : ℚ) * coeff (m + 3) S) = 0 := by
  have h := congrArg (coeff (m + 3)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  skip
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

theorem hf1 : coeff 1 F = (0 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (1 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (2 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (4 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (10 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (28 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (1 : ℚ) := by rw [a_eq]; exact hf2

theorem ha1 : a 1 = (2 : ℚ) := by rw [a_eq]; exact hf3

theorem ha2 : a 2 = (4 : ℚ) := by rw [a_eq]; exact hf4

theorem ha3 : a 3 = (10 : ℚ) := by rw [a_eq]; exact hf5

theorem ha4 : a 4 = (28 : ℚ) := by rw [a_eq]; exact hf6

noncomputable def Mv (n : ℕ) : ℚ := ((n : ℚ) + 2) * a n + (-4 * (n : ℚ) - 2) * a (n - 1) + (2 * (n : ℚ) - 2) * a (n - 2)
      + (-4 * (n : ℚ) + 10) * a (n - 3) + ((n : ℚ) - 4) * a (n - 4)

theorem base4 : Mv 4 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4]

theorem certQ (k : ℕ) : (0) * Mv (k + 4) + ((-4 : ℚ)) * Mv (k + 5) = 0 := by
  unfold Mv
  rw [show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 4 - 3 = k + 1 from by omega, show k + 4 - 4 = k from by omega, show k + 5 - 1 = k + 4 from by omega, show k + 5 - 2 = k + 3 from by omega, show k + 5 - 3 = k + 2 from by omega, show k + 5 - 4 = k + 1 from by omega]
  simp only [a_eq]
  have r1_47 := rel1 (k)
  have r1_48 := rel1 (k + 1)
  have r1_49 := rel1 (k + 2)
  have r1_50 := rel1 (k + 3)
  have r1_51 := rel1 (k + 4)
  have r2_50 := rel2 (k + 2)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_47 r1_48 r1_49 r1_50 r1_51 r2_50 ⊢
  push_cast at r1_47 r1_48 r1_49 r1_50 r1_51 r2_50 ⊢
  linear_combination ((6 : ℚ) + (-2 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_47 + ((-12 : ℚ) + (8 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_48 + ((-4 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_49 + ((12 : ℚ) + (8 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_50 + ((-6 : ℚ) + (-2 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_51 + ((1 : ℚ)) * r2_50

theorem Mv_zero : ∀ n : ℕ, 4 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 5
    · interval_cases n
      · exact base4
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 4) = 0 := ih _ (by omega) (by omega)
      have hq : ((-4 : ℚ)) ≠ 0 := by
        have e : ((-4 : ℚ)) = -((4 : ℚ)) := by ring
        rw [e, neg_ne_zero]
        positivity
      have hm : ((-4 : ℚ)) * Mv (k + 5) = 0 := by linear_combination hc - (0) * h0
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem mainQ : ∀ n : ℕ, 4 ≤ n → ((n : ℚ) + 2) * a n + (-4 * (n : ℚ) - 2) * a (n - 1) + (2 * (n : ℚ) - 2) * a (n - 2)
      + (-4 * (n : ℚ) + 10) * a (n - 3) + ((n : ℚ) - 4) * a (n - 4) = 0 := fun n hn => Mv_zero n hn

theorem main' : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 2) * a n - 2 * (2 * (n : ℤ) + 1) * a (n - 1) + 2 * ((n : ℤ) - 1) * a (n - 2)
      + 2 * (5 - 2 * (n : ℤ)) * a (n - 3) + ((n : ℤ) - 4) * a (n - 4) = 0 := by
  intro n hn
  have h := mainQ n hn
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination h

end OMA.P_oeis_a187256

theorem OMA.solution : type_of% @OMA.S_oeis_a187256.main := OMA.P_oeis_a187256.main'
