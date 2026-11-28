import OMAStatements.S_oeis_a176756
import Mathlib

-- Problem: A176756, R. J. Mathar's conjectured recurrence for a(0) = 1, a(1) = 4,
-- a(n+2) = Sum_{p=0..n+1} a(p) a(n+1-p) + (0 n + -2).
-- Upstream: formal-conjectures statements/oeis-a176756.lean (declaration OMA.S_oeis_a176756.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof idea: the g.f. G satisfies x G^2 - G + 1 + (3) x + x^2 L = 0 with (1 - x)^2 L linear (Q1, hLg),
-- so U = (1 - x)^2 (1 - 2 x G) satisfies U^2 = R and U(0) = 1, hence U = sqrt(R) (T_eq) and
-- x G = ((1 - x)^2 - S) / (2 (1 - x)^2). With 2 R S' = R' S the recurrence follows from an explicit
-- operator certificate (and an induction from exactly computed initial values).

namespace OMA.P_oeis_a176756

open OMA.S_oeis_a176756 PowerSeries

noncomputable def R : PowerSeries ℚ := 1 - 8 * X + 10 * X ^ 2 + 28 * X ^ 3 - 79 * X ^ 4 + 68 * X ^ 5 - 20 * X ^ 6

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

theorem hRC : R = C (1 : ℚ) + C (-8 : ℚ) * X ^ 1 + C (10 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3 + C (-79 : ℚ) * X ^ 4 + C (68 : ℚ) * X ^ 5 + C (-20 : ℚ) * X ^ 6 := by
  simp only [R, map_one, map_neg, map_ofNat] <;> ring

theorem hDR : d⁄dX ℚ R = C (-8 : ℚ) + C (20 : ℚ) * X ^ 1 + C (84 : ℚ) * X ^ 2 + C (-316 : ℚ) * X ^ 3 + C (340 : ℚ) * X ^ 4 + C (-120 : ℚ) * X ^ 5 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  try push_cast
  try ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-16 : ℚ) * X ^ 1 * d⁄dX ℚ S + C (20 : ℚ) * X ^ 2 * d⁄dX ℚ S + C (56 : ℚ) * X ^ 3 * d⁄dX ℚ S + C (-158 : ℚ) * X ^ 4 * d⁄dX ℚ S + C (136 : ℚ) * X ^ 5 * d⁄dX ℚ S + C (-40 : ℚ) * X ^ 6 * d⁄dX ℚ S - (C (-8 : ℚ) * S + C (20 : ℚ) * X ^ 1 * S + C (84 : ℚ) * X ^ 2 * S + C (-316 : ℚ) * X ^ 3 * S + C (340 : ℚ) * X ^ 4 * S + C (-120 : ℚ) * X ^ 5 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 7) S * ((m : ℚ) + 7)) + (-16 : ℚ) * (coeff (m + 6) S * ((m : ℚ) + 6)) + (20 : ℚ) * (coeff (m + 5) S * ((m : ℚ) + 5)) + (56 : ℚ) * (coeff (m + 4) S * ((m : ℚ) + 4)) + (-158 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (136 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (-40 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-8 : ℚ) * coeff (m + 6) S + (20 : ℚ) * coeff (m + 5) S + (84 : ℚ) * coeff (m + 4) S + (-316 : ℚ) * coeff (m + 3) S + (340 : ℚ) * coeff (m + 2) S + (-120 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 6)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 6 - 1 = m + 5 from by omega, show m + 6 - 2 = m + 4 from by omega, show m + 6 - 3 = m + 3 from by omega, show m + 6 - 4 = m + 2 from by omega, show m + 6 - 5 = m + 1 from by omega, show m + 6 - 6 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((1 - 2 * X + X ^ 2 - S) * (2 - 4 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

theorem len_aList : ∀ m : ℕ, (aList m).length = m + 1
  | 0 => rfl
  | 1 => rfl
  | m + 2 => by
    rw [aList]
    simp only [List.length_append, List.length_singleton]
    rw [len_aList (m + 1)]

theorem getD_aList : ∀ m p : ℕ, p ≤ m → (aList m).getD p 0 = a p
  | 0, p, h => by
    obtain rfl : p = 0 := by omega
    rfl
  | 1, p, h => by
    rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl <;> rfl
  | m + 2, p, h => by
    rcases Nat.lt_or_ge p (m + 2) with hp | hp
    · rw [aList]
      try dsimp only
      rw [List.getD_append _ _ _ _ (by rw [len_aList]; omega)]
      exact getD_aList (m + 1) p (by omega)
    · obtain rfl : p = m + 2 := by omega
      rfl

theorem rec_a (n : ℕ) : a (n + 2) = (∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p)) - 2 := by
  have h : a (n + 2) = (aList (n + 2)).getD (n + 2) 0 := rfl
  rw [h, aList]
  try dsimp only
  rw [List.getD_append_right _ _ _ _ (by rw [len_aList]), len_aList, Nat.sub_self]
  simp only [List.getD_cons_zero]
  have hs : ∑ p ∈ Finset.range (n + 2), (aList (n + 1)).getD p 0 * (aList (n + 1)).getD (n + 1 - p) 0
      = ∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_range] at hp
    rw [getD_aList (n + 1) p (by omega), getD_aList (n + 1) (n + 1 - p) (by omega)]
  rw [hs]

noncomputable def G : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))

noncomputable def Lg : ℚ⟦X⟧ := PowerSeries.mk (fun n => (0 : ℚ) * n + -2)

theorem hLg : (1 - X) ^ 2 * Lg = C (-2 : ℚ) + C (2 : ℚ) * X := by
  ext n
  rcases n with _ | _ | n
  · simp [Lg, sq, sub_mul, mul_sub, coeff_X_pow_mul', coeff_C]
  · have e : (1 - X) ^ 2 * Lg = Lg - C (2 : ℚ) * (X * Lg) + X ^ 2 * Lg := by
      simp only [map_ofNat]
      ring
    rw [e, map_add, map_sub, coeff_C_mul, coeff_succ_X_mul]
    simp [Lg, coeff_X_pow_mul', coeff_X, coeff_C]
    ring
  · have e : (1 - X) ^ 2 * Lg = Lg - C (2 : ℚ) * (X * Lg) + X ^ 2 * Lg := by
      simp only [map_ofNat]
      ring
    rw [e, map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, show n + 1 + 1 = n + 2 from rfl,
      coeff_X_pow_mul]
    simp [Lg, coeff_X, coeff_C]
    push_cast
    ring

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

theorem Q1 : X * G ^ 2 - G + 1 + C (3 : ℚ) * X + X ^ 2 * Lg = 0 := by
  ext n
  rw [map_zero]
  rcases n with _ | _ | n
  · simp [G, Lg, a, aList, coeff_X_pow_mul']
  · have e1 : coeff 1 (X * G ^ 2) = coeff 0 (G ^ 2) := coeff_succ_X_mul _ _
    have e0 : coeff 0 (G ^ 2) = 1 := by simp [G, a, aList]
    have e3 : coeff 1 G = 4 := by simp [G, a, aList]
    have e4 : coeff 1 (C (3 : ℚ) * X) = 3 := by rw [coeff_C_mul, coeff_X]; simp
    have e5 : coeff 1 (X ^ 2 * Lg) = 0 := by simp [coeff_X_pow_mul']
    have e6 : coeff 1 (1 : ℚ⟦X⟧) = 0 := by simp [coeff_one]
    rw [map_add, map_add, map_add, map_sub, e1, e0, e3, e4, e5, e6]
    norm_num
  · have h2 : coeff (n + 1) (G ^ 2) = ∑ p ∈ Finset.range (n + 2), (a p : ℚ) * a (n + 1 - p) := by
      rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [G]
    have h3 : (a (n + 2) : ℚ) = (∑ p ∈ Finset.range (n + 2), (a p : ℚ) * a (n + 1 - p)) + (0 : ℚ) * n + -2 := by
      rw [rec_a]
      push_cast
      ring
    have e1 : coeff (n + 2) (X * G ^ 2) = coeff (n + 1) (G ^ 2) := coeff_succ_X_mul _ _
    have e3 : coeff (n + 2) G = (a (n + 2) : ℚ) := by simp [G]
    have e4 : coeff (n + 2) (C (3 : ℚ) * X) = 0 := by rw [coeff_C_mul, coeff_X]; simp
    have e5 : coeff (n + 2) (X ^ 2 * Lg) = (0 : ℚ) * n + -2 := by
      rw [coeff_X_pow_mul]
      simp [Lg]
    have e6 : coeff (n + 2) (1 : ℚ⟦X⟧) = 0 := by simp [coeff_one]
    rw [map_add, map_add, map_add, map_sub, e1, e3, e4, e5, e6, h2, h3]
    ring

theorem T_eq : (1 - X) ^ 2 - 2 * X * (1 - X) ^ 2 * G = S := by
  have q := Q1
  have l := hLg
  simp only [map_ofNat, map_neg, map_one, map_zero, map_intCast] at q l
  have hT : ((1 - X) ^ 2 - 2 * X * (1 - X) ^ 2 * G) ^ 2 = R := by
    unfold R
    linear_combination (4 * X * (1 - X) ^ 4) * q - (4 * X ^ 3 * (1 - X) ^ 2) * l
  have h : ((1 - X) ^ 2 - 2 * X * (1 - X) ^ 2 * G - S) * ((1 - X) ^ 2 - 2 * X * (1 - X) ^ 2 * G + S) = 0 := by
    linear_combination hT - S_sq
  rcases mul_eq_zero.mp h with h1 | h1
  · exact sub_eq_zero.mp h1
  · exfalso
    have h2 := congrArg constantCoeff h1
    norm_num [S_const0] at h2

theorem a_eq (n : ℕ) : (a n : ℚ) = coeff (n + 1) F := by
  have hF2 : F = X * G := by
    unfold F
    have e : 1 - 2 * X + X ^ 2 - S = X * G * (2 - 4 * X + 2 * X ^ 2) := by
      rw [← T_eq]
      ring
    rw [e, mul_assoc, PowerSeries.mul_inv_cancel _ (by
      rw [show (2 - 4 * X + 2 * X ^ 2 : ℚ⟦X⟧) = C (2 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (2 : ℚ) * X ^ 2 from by
        simp only [map_neg, map_ofNat] <;> ring]
      simp), mul_one]
  rw [hF2, coeff_succ_X_mul]
  simp [G]

theorem hF : F * (2 - 4 * X + 2 * X ^ 2 : ℚ⟦X⟧) = 1 - 2 * X + X ^ 2 - S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 - 4 * X + 2 * X ^ 2 : ℚ⟦X⟧) = C (2 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (2 : ℚ) * X ^ 2 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (-4 : ℚ) * X ^ 1 * F + C (2 : ℚ) * X ^ 2 * F - (C (-1 : ℚ) * S) - (C (1 : ℚ) + C (-2 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 2) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 3) F + (-4 : ℚ) * coeff (m + 2) F + (2 : ℚ) * coeff (m + 1) F - ((-1 : ℚ) * coeff (m + 3) S) = 0 := by
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

theorem hs1 : coeff 1 S = (-4 : ℚ) := by
  have h := congrArg (coeff 0) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0] at h ⊢ <;> linarith

theorem hs2 : coeff 2 S = (-3 : ℚ) := by
  have h := congrArg (coeff 1) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1] at h ⊢ <;> linarith

theorem hs3 : coeff 3 S = (2 : ℚ) := by
  have h := congrArg (coeff 2) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2] at h ⊢ <;> linarith

theorem hs4 : coeff 4 S = (-36 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hs5 : coeff 5 S = (-104 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hs6 : coeff 6 S = (-536 : ℚ) := by
  have h := congrArg (coeff 5) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hs7 : coeff 7 S = (-2384 : ℚ) := by
  have h := congrArg (coeff 6) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at h ⊢ <;> linarith

theorem hs8 : coeff 8 S = (-11584 : ℚ) := by
  have h := congrArg (coeff 7) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (0 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (1 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (4 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (6 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (26 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (98 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (438 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (1970 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (9294 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (1 : ℚ) := by rw [a_eq]; exact hf1

theorem ha1 : a 1 = (4 : ℚ) := by rw [a_eq]; exact hf2

theorem ha2 : a 2 = (6 : ℚ) := by rw [a_eq]; exact hf3

theorem ha3 : a 3 = (26 : ℚ) := by rw [a_eq]; exact hf4

theorem ha4 : a 4 = (98 : ℚ) := by rw [a_eq]; exact hf5

theorem ha5 : a 5 = (438 : ℚ) := by rw [a_eq]; exact hf6

theorem ha6 : a 6 = (1970 : ℚ) := by rw [a_eq]; exact hf7

theorem ha7 : a 7 = (9294 : ℚ) := by rw [a_eq]; exact hf8

noncomputable def Mv (n : ℕ) : ℚ := ((n : ℚ) + 1) * a n
      + 2 * (-3 * (n : ℚ) + 1) * a (n - 1)
      + (-3 * (n : ℚ) + 11) * a (n - 2)
      + 2 * (14 * (n : ℚ) - 45) * a (n - 3)
      + 20 * (-(n : ℚ) + 4) * a (n - 4)

theorem base4 : Mv 4 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]

theorem base5 : Mv 5 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]

theorem base6 : Mv 6 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]

theorem base7 : Mv 7 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]

theorem certQ (k : ℕ) : ((-4 : ℚ)) * Mv (k + 4) + ((16 : ℚ)) * Mv (k + 5) + ((-24 : ℚ)) * Mv (k + 6) + ((16 : ℚ)) * Mv (k + 7) + ((-4 : ℚ)) * Mv (k + 8) = 0 := by
  unfold Mv
  rw [show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 4 - 3 = k + 1 from by omega, show k + 4 - 4 = k from by omega, show k + 5 - 1 = k + 4 from by omega, show k + 5 - 2 = k + 3 from by omega, show k + 5 - 3 = k + 2 from by omega, show k + 5 - 4 = k + 1 from by omega, show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega, show k + 6 - 3 = k + 3 from by omega, show k + 6 - 4 = k + 2 from by omega, show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega, show k + 7 - 3 = k + 4 from by omega, show k + 7 - 4 = k + 3 from by omega, show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 8 - 4 = k + 4 from by omega]
  simp only [a_eq]
  have r1_48 := rel1 (k)
  have r1_49 := rel1 (k + 1)
  have r1_50 := rel1 (k + 2)
  have r1_51 := rel1 (k + 3)
  have r1_52 := rel1 (k + 4)
  have r1_53 := rel1 (k + 5)
  have r1_54 := rel1 (k + 6)
  have r2_53 := rel2 (k + 2)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_48 r1_49 r1_50 r1_51 r1_52 r1_53 r1_54 r2_53 ⊢
  push_cast at r1_48 r1_49 r1_50 r1_51 r1_52 r1_53 r1_54 r2_53 ⊢
  linear_combination ((-160 : ℚ) + (40 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_48 + ((340 : ℚ) + (-136 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_49 + ((-158 : ℚ) + (158 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_50 + ((-28 : ℚ) + (-56 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_51 + ((-40 : ℚ) + (-20 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_52 + ((56 : ℚ) + (16 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_53 + ((-10 : ℚ) + (-2 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_54 + ((1 : ℚ)) * r2_53

theorem Mv_zero : ∀ n : ℕ, 4 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 8
    · interval_cases n
      · exact base4
      · exact base5
      · exact base6
      · exact base7
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 4) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 5) = 0 := ih _ (by omega) (by omega)
      have h2 : Mv (k + 6) = 0 := ih _ (by omega) (by omega)
      have h3 : Mv (k + 7) = 0 := ih _ (by omega) (by omega)
      have hq : ((-4 : ℚ)) ≠ 0 := by
        have e : ((-4 : ℚ)) = -((4 : ℚ)) := by ring
        rw [e, neg_ne_zero]
        positivity
      have hm : ((-4 : ℚ)) * Mv (k + 8) = 0 := by linear_combination hc - ((-4 : ℚ)) * h0 - ((16 : ℚ)) * h1 - ((-24 : ℚ)) * h2 - ((16 : ℚ)) * h3
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem mainQ : ∀ n : ℕ, 4 ≤ n → ((n : ℚ) + 1) * a n
      + 2 * (-3 * (n : ℚ) + 1) * a (n - 1)
      + (-3 * (n : ℚ) + 11) * a (n - 2)
      + 2 * (14 * (n : ℚ) - 45) * a (n - 3)
      + 20 * (-(n : ℚ) + 4) * a (n - 4) = 0 := fun n hn => Mv_zero n hn

theorem main' : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 1) * a n
      + 2 * (-3 * (n : ℤ) + 1) * a (n - 1)
      + (-3 * (n : ℤ) + 11) * a (n - 2)
      + 2 * (14 * (n : ℤ) - 45) * a (n - 3)
      + 20 * (-(n : ℤ) + 4) * a (n - 4) = 0 := by
  intro n hn
  have h := mainQ n hn
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination h

end OMA.P_oeis_a176756

theorem OMA.solution : type_of% @OMA.S_oeis_a176756.main := OMA.P_oeis_a176756.main'
