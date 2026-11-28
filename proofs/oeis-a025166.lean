import OMAStatements.S_oeis_a025166

-- Problem: A025166: Expansion of e.g.f. -exp(-x/(1-2*x))/(1-2*x).
-- Upstream: formal-conjectures statements/oeis-a025166.lean:0 (declaration OMA.S_oeis_a025166.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The derivative of exp(R) is exp(R) R', by the chain rule for substitution of power series.
Differentiating the two defining relations and eliminating exp(R), R and R' gives a first order
linear differential equation c1 F' + c0 F = 0 with polynomial coefficients. A polynomial
combination of this equation and its derivative is a second order equation whose coefficient of
a power of x, written through a(n) = n! [x^n] F, is the recurrence. -/

namespace A025166Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S * (1 - 2 * X) = -X)
    (hG : G * (1 - 2 * X) = (-1) * (PowerSeries.exp ℚ).subst S) :
    (1 - 4 * X + 4 * X ^ 2) * derivative ℚ G + (-1 + 4 * X) * G = 0 := by
  have hS0 : constantCoeff S = 0 := by
    have h := congrArg constantCoeff hS
    simpa using h
  have hsub : HasSubst S := HasSubst.of_constantCoeff_zero' hS0
  have hE : derivative ℚ ((PowerSeries.exp ℚ).subst S) = (PowerSeries.exp ℚ).subst S * derivative ℚ S := by
    rw [derivative_subst hsub, derivative_exp]
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have hL1 : derivative ℚ (S * (1 - 2 * X : ℚ⟦X⟧)) = derivative ℚ S * (1 - 2 * X) + S * (-2) := by
    simp [Derivation.leibniz, d2]
    ring
  have hR1 : derivative ℚ (-1 * X : ℚ⟦X⟧) = -1 := by
    simp
  have hSp : S * (1 - 2 * X : ℚ⟦X⟧) = (-1 * X : ℚ⟦X⟧) := by linear_combination hS
  have hdS : derivative ℚ S * (1 - 2 * X) + S * (-2) = -1 := by rw [← hL1, hSp, hR1]
  have hL2 : derivative ℚ (G * (1 - 2 * X : ℚ⟦X⟧)) = derivative ℚ G * (1 - 2 * X) + G * (-2) := by
    simp [Derivation.leibniz, d2]
    ring
  have hR2 : derivative ℚ ((-1 : ℚ⟦X⟧) * (PowerSeries.exp ℚ).subst S) =
      (0) * (PowerSeries.exp ℚ).subst S + (-1) * derivative ℚ ((PowerSeries.exp ℚ).subst S) := by
    simp
  have hGp : G * (1 - 2 * X : ℚ⟦X⟧) = (-1 : ℚ⟦X⟧) * (PowerSeries.exp ℚ).subst S := by linear_combination hG
  have hdG : derivative ℚ G * (1 - 2 * X) + G * (-2) = (0) * (PowerSeries.exp ℚ).subst S + (-1) * derivative ℚ ((PowerSeries.exp ℚ).subst S) := by
    rw [← hL2, ← hR2, hGp]
  have hfull : (1 - 2 * X) * ((1 - 4 * X + 4 * X ^ 2) * derivative ℚ G + (-1 + 4 * X) * G) = 0 := by
    linear_combination ((1) + (-4) * X + (4) * X ^ 2) * hdG +
      ((-1) + (4) * X + (-4) * X ^ 2) * hE +
      ((-1) * ((PowerSeries.exp ℚ).subst S) + (2) * X * ((PowerSeries.exp ℚ).subst S)) * hdS +
      ((-2) * ((PowerSeries.exp ℚ).subst S)) * hS +
      ((1)) * hG
  have hM : (1 - 2 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hM
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S * (1 - 2 * X) = -X)
    (hG : G * (1 - 2 * X) = (-1) * (PowerSeries.exp ℚ).subst S) :
    (X ^ 2 - 4 * X ^ 3 + 4 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-5 * X ^ 2 + 12 * X ^ 3) * derivative ℚ G + (4 * X ^ 2) * G = 0 := by
  have h := key S G hS hG
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hL : derivative ℚ ((1 - 4 * X + 4 * (X * X) : ℚ⟦X⟧) * derivative ℚ G + (-1 + 4 * X : ℚ⟦X⟧) * G) =
      (-4 + 8 * X) * derivative ℚ G + (1 - 4 * X + 4 * X ^ 2) * derivative ℚ (derivative ℚ G) + (4) * G + (-1 + 4 * X) * derivative ℚ G := by
    simp [Derivation.leibniz, d4]
    ring
  have h2 : (1 - 4 * X + 4 * (X * X) : ℚ⟦X⟧) * derivative ℚ G + (-1 + 4 * X : ℚ⟦X⟧) * G = 0 := by linear_combination h
  have hd : (-4 + 8 * X) * derivative ℚ G + (1 - 4 * X + 4 * X ^ 2) * derivative ℚ (derivative ℚ G) + (4) * G + (-1 + 4 * X) * derivative ℚ G = 0 := by
    rw [← hL, h2, map_zero]
  linear_combination (X ^ 2) * hd + (0) * h

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S * (1 - 2 * X) = -X)
    (hG : G * (1 - 2 * X) = (-1) * (PowerSeries.exp ℚ).subst S) :
    derivative ℚ (derivative ℚ G) * X * X * C 1 + derivative ℚ (derivative ℚ G) * X * X * X * C (-4) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 4 + derivative ℚ G * X * X * C (-5) +
      derivative ℚ G * X * X * X * C 12 + G * X * X * C 4 =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S * (1 - 2 * X) = -X)
    (hG : G * (1 - 2 * X) = (-1) * (PowerSeries.exp ℚ).subst S) (m : ℕ) :
    1 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      4 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-5) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      12 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 4 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S * (1 - 2 * X) = -X)
    (hG : G * (1 - 2 * X) = (-1) * (PowerSeries.exp ℚ).subst S) :
    2 * coeff (0 + 1 + 1) G + (-5) * coeff (0 + 1) G +
      4 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S * (1 - 2 * X) = -X)
    (hG : G * (1 - 2 * X) = (-1) * (PowerSeries.exp ℚ).subst S) :
    6 * coeff (0 + 1 + 1 + 1) G + (-8) * coeff (0 + 1 + 1) G +
      (-10) * coeff (0 + 1 + 1) G + 12 * coeff (0 + 1) G +
      4 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A025166Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a025166.main := by
  intro R F hR hF n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  unfold OMA.S_oeis_a025166.a
  cases m with
  | zero =>
    have r := A025166Aux.relE0 R F hR hF
    simp only [Nat.factorial_succ, Nat.factorial_zero]
    push_cast
    linear_combination (1 : ℚ) * r
  | succ m =>
    cases m with
    | zero =>
      have r := A025166Aux.relE1 R F hR hF
      simp only [Nat.factorial_succ, Nat.factorial_zero]
      push_cast
      linear_combination (1 : ℚ) * r
    | succ m =>
      have r := A025166Aux.rel R F hR hF m
      simp only [Nat.factorial_succ]
      push_cast
      linear_combination (((m : ℚ) + 1) * ((m : ℚ) + 2) * (m.factorial : ℚ)) * r
