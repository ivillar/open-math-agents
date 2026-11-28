import OMAStatements.S_oeis_a257290
import Mathlib

-- Problem: A257290, R. J. Mathar's conjectured recurrence for the 3-Motzkin path counts
-- a(n+2) = 3 a(n+1) + Sum_{k=0..n} a(k) a(n-k).
-- Upstream: formal-conjectures statements/oeis-a257290.lean (declaration OMA.S_oeis_a257290.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof idea: the g.f. F satisfies x^2 F^2 + (3x - 1) F + 1 - 3x = 0 (quad), so U = 1 - 3x - 2x^2 F
-- satisfies U^2 = R = 1 - 6x + 5x^2 + 12x^3 and U(0) = 1; hence U = S = sqrt(R) (T_eq). With
-- 2 R S' = R' S (rel2) and 2x^2 F = 1 - 3x - S (rel1), the recurrence is an explicit polynomial
-- combination of shifted instances of rel1 and rel2.

namespace OMA.P_oeis_a257290

open OMA.S_oeis_a257290 PowerSeries

noncomputable def R : PowerSeries ℚ := 1 - 6 * X + 5 * X ^ 2 + 12 * X ^ 3

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

theorem hRC : R = C (1 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (5 : ℚ) * X ^ 2 + C (12 : ℚ) * X ^ 3 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-6 : ℚ) + C (10 : ℚ) * X ^ 1 + C (36 : ℚ) * X ^ 2 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-12 : ℚ) * X ^ 1 * d⁄dX ℚ S + C (10 : ℚ) * X ^ 2 * d⁄dX ℚ S + C (24 : ℚ) * X ^ 3 * d⁄dX ℚ S - (C (-6 : ℚ) * S + C (10 : ℚ) * X ^ 1 * S + C (36 : ℚ) * X ^ 2 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 4) S * ((m : ℚ) + 4)) + (-12 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (10 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (24 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-6 : ℚ) * coeff (m + 3) S + (10 : ℚ) * coeff (m + 2) S + (36 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 3)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega, show m + 3 - 3 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))

theorem a_eq (n : ℕ) : (a n : ℚ) = coeff n F := by simp [F]

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

theorem quad : X ^ 2 * F ^ 2 + C (3 : ℚ) * (X * F) - F + 1 - C (3 : ℚ) * X = 0 := by
  ext n
  rw [map_zero]
  rcases n with _ | _ | n
  · simp [F, a]
  · have e1 : coeff 1 (X ^ 2 * F ^ 2) = 0 := by simp [coeff_X_pow_mul']
    have e2 : coeff 1 (C (3 : ℚ) * (X * F)) = 3 * coeff 0 F := by
      rw [coeff_C_mul, coeff_succ_X_mul]
    have e3 : coeff 0 F = 1 := by simp [F, a]
    have e4 : coeff 1 F = 0 := by simp [F, a]
    have e5 : coeff 1 (C (3 : ℚ) * X) = 3 := by rw [coeff_C_mul, coeff_X]; simp
    have e6 : coeff 1 (1 : ℚ⟦X⟧) = 0 := by simp [coeff_one]
    rw [map_sub, map_add, map_sub, map_add, e1, e2, e3, e4, e5, e6]
    ring
  · have h2 : coeff n (F ^ 2) = ∑ k ∈ Finset.range (n + 1), (a k : ℚ) * a (n - k) := by
      rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [F]
    have h3 : (a (n + 2) : ℚ) = 3 * (a (n + 1) : ℚ) + ∑ k ∈ Finset.range (n + 1), (a k : ℚ) * a (n - k) := by
      rw [a]
      push_cast
      rw [Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ) * a (n - k))]
    have e1 : coeff (n + 2) (X ^ 2 * F ^ 2) = coeff n (F ^ 2) := by simp [coeff_X_pow_mul']
    have e2 : coeff (n + 2) (C (3 : ℚ) * (X * F)) = 3 * (a (n + 1) : ℚ) := by
      rw [coeff_C_mul, coeff_succ_X_mul]
      simp [F]
    have e3 : coeff (n + 2) F = (a (n + 2) : ℚ) := by simp [F]
    have e4 : coeff (n + 2) (1 : ℚ⟦X⟧) = 0 := by simp [coeff_one]
    have e5 : coeff (n + 2) (C (3 : ℚ) * X) = 0 := by rw [coeff_C_mul, coeff_X]; simp
    rw [map_sub, map_add, map_sub, map_add, e1, e2, e3, e4, e5, h2, h3]
    ring

theorem T_eq : 1 - 3 * X - 2 * X ^ 2 * F = S := by
  have q := quad
  simp only [map_ofNat] at q
  have hT : (1 - 3 * X - 2 * X ^ 2 * F) ^ 2 = R := by
    unfold R
    linear_combination (4 * X ^ 2) * q
  have h : (1 - 3 * X - 2 * X ^ 2 * F - S) * (1 - 3 * X - 2 * X ^ 2 * F + S) = 0 := by
    linear_combination hT - S_sq
  rcases mul_eq_zero.mp h with h1 | h1
  · exact sub_eq_zero.mp h1
  · exfalso
    have h2 := congrArg constantCoeff h1
    norm_num [S_const] at h2

theorem E1 : C (2 : ℚ) * X ^ 2 * F - (C (-1 : ℚ) * S) - (C (1 : ℚ) + C (-3 : ℚ) * X ^ 1) = 0 := by
  simp only [map_one, map_neg, map_ofNat]
  linear_combination (-1 : ℚ⟦X⟧) * T_eq

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m) F - ((-1 : ℚ) * coeff (m + 2) S) = 0 := by
  have h := congrArg (coeff (m + 2)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 2 - 2 = m from by omega] at h
  linear_combination h

theorem mainQ : ∀ n : ℕ, 3 ≤ n → ((n : ℚ) + 2) * a n + (-6 * (n : ℚ) - 3) * a (n - 1) + (5 * (n : ℚ) - 5) * a (n - 2)
      + (12 * (n : ℚ) - 30) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 from by omega, show k + 3 - 2 = k + 1 from by omega, show k + 3 - 3 = k from by omega]
  simp only [a_eq]
  have r1_49 := rel1 (k)
  have r1_50 := rel1 (k + 1)
  have r1_51 := rel1 (k + 2)
  have r1_52 := rel1 (k + 3)
  have r2_51 := rel2 (k + 1)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_49 r1_50 r1_51 r1_52 r2_51 ⊢
  push_cast at r1_49 r1_50 r1_51 r1_52 r2_51 ⊢
  linear_combination ((-15 : ℚ) + (6 : ℚ) * ((k : ℚ) + 3) ^ 1) * r1_49 + ((-5 / 2 : ℚ) + (5 / 2 : ℚ) * ((k : ℚ) + 3) ^ 1) * r1_50 + ((-3 / 2 : ℚ) + (-3 : ℚ) * ((k : ℚ) + 3) ^ 1) * r1_51 + ((1 : ℚ) + (1 / 2 : ℚ) * ((k : ℚ) + 3) ^ 1) * r1_52 + ((-1 / 4 : ℚ)) * r2_51

theorem main' : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 2) * a n + 3 * (-2 * (n : ℤ) - 1) * a (n - 1) + 5 * ((n : ℤ) - 1) * a (n - 2)
      + 6 * (2 * (n : ℤ) - 5) * a (n - 3) = 0 := by
  intro n hn
  have h := mainQ n hn
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination h

end OMA.P_oeis_a257290

theorem OMA.solution : type_of% @OMA.S_oeis_a257290.main := OMA.P_oeis_a257290.main'
