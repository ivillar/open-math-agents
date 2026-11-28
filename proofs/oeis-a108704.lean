import OMAStatements.S_oeis_a108704

-- Problem: A108704: Number of partitions of 112233...nn into n pairs.
-- Upstream: formal-conjectures statements/oeis-a108704.lean:0 (declaration OMA.S_oeis_a108704.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The derivative of exp(R) is exp(R) R', by the chain rule for substitution of power series.
Differentiating the three defining relations S^2 = 1 - 2x, 2R = x^2 and F S = exp(R) and eliminating
exp(R), R', S and S' gives the first order linear differential equation
(2 - 4x) F' = (2 + 2x - 4x^2) F. Its coefficient of x^(m+2), written through a(n) = n! [x^n] F, is the
recurrence at n = m + 3. -/

namespace A108704Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S R F : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X) (hR : 2 * R = X ^ 2)
    (hF : F * S = (PowerSeries.exp ℚ).subst R) :
    (2 - 4 * X) * derivative ℚ F + (-2 - 2 * X + 4 * X ^ 2) * F = 0 := by
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have hR0 : constantCoeff R = 0 := by
    have h := congrArg constantCoeff hR
    simp [k2] at h
    linarith
  have hsub : HasSubst R := HasSubst.of_constantCoeff_zero' hR0
  have hE : derivative ℚ ((PowerSeries.exp ℚ).subst R) =
      (PowerSeries.exp ℚ).subst R * derivative ℚ R := by
    rw [derivative_subst hsub, derivative_exp]
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have hLR : derivative ℚ (2 * R : ℚ⟦X⟧) = 2 * derivative ℚ R := by
    simp [Derivation.leibniz, d2]
  have hRR : derivative ℚ (X * X : ℚ⟦X⟧) = 2 * X := by
    simp [Derivation.leibniz]
    ring
  have hRp : (2 * R : ℚ⟦X⟧) = X * X := by linear_combination hR
  have hdR : 2 * derivative ℚ R = 2 * X := by rw [← hLR, hRp, hRR]
  have hLS : derivative ℚ (S * S : ℚ⟦X⟧) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hRS : derivative ℚ (1 - 2 * X : ℚ⟦X⟧) = -2 := by
    simp [Derivation.leibniz, d2]
  have hSp : (S * S : ℚ⟦X⟧) = 1 - 2 * X := by linear_combination hS
  have hdS : 2 * S * derivative ℚ S = -2 := by rw [← hLS, hSp, hRS]
  have hLF : derivative ℚ (F * S) = derivative ℚ F * S + F * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdF : derivative ℚ F * S + F * derivative ℚ S =
      (PowerSeries.exp ℚ).subst R * derivative ℚ R := by
    rw [← hLF, hF, hE]
  linear_combination (2 * S) * hdF - (2 * derivative ℚ F - 2 * F * derivative ℚ R) * hS -
    F * hdS - (2 * S * derivative ℚ R) * hF + ((1 - 2 * X) * F) * hdR

set_option maxHeartbeats 4000000 in
theorem keyC (S R F : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X) (hR : 2 * R = X ^ 2)
    (hF : F * S = (PowerSeries.exp ℚ).subst R) :
    derivative ℚ F * C 2 + derivative ℚ F * X * C (-4) + F * C (-2) + F * X * C (-2) +
      F * X * X * C 4 = 0 := by
  have h := key S R F hS hR hF
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S R F : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X) (hR : 2 * R = X ^ 2)
    (hF : F * S = (PowerSeries.exp ℚ).subst R) (m : ℕ) :
    2 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) F + (-4) * ((m : ℚ) + 2) * coeff (m + 1 + 1) F +
      (-2) * coeff (m + 1 + 1) F + (-2) * coeff (m + 1) F + 4 * coeff m F = 0 := by
  have h := congrArg (coeff (m + 1 + 1)) (keyC S R F hS hR hF)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

end A108704Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a108704.main := by
  intro S R F hS _ hR hF n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  unfold OMA.S_oeis_a108704.a
  have r := A108704Aux.rel S R F hS hR hF m
  simp only [Nat.factorial_succ]
  push_cast
  linear_combination ((1 / 2 : ℚ) * ((m : ℚ) + 1) * ((m : ℚ) + 2) * (m.factorial : ℚ)) * r
