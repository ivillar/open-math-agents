import OMAStatements.S_oeis_a097188

-- Problem: A097188: G.f. A(x) satisfies A057083(x*A(x)) = A(x) and so equals the ratio of the g.f.s of any two adjacent diagonals of triangle A097186.
-- Upstream: formal-conjectures statements/oeis-a097188.lean:0 (declaration OMA.S_oeis_a097188.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A097188Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-3 * X : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (X - 9 * X ^ 2) * derivative ℚ G + (1 - 6 * X) * G =
      1 := by
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have hp0 : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-3 * X : ℚ⟦X⟧) * G * G + (3 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-3 * X : ℚ⟦X⟧) * G * G + (3 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-6 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-3 : ℚ⟦X⟧) * G ^ 2 + (9 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (6 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d3]
    ring
  have hd1 : (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-6 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-3 : ℚ⟦X⟧) * G ^ 2 + (9 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (6 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hfull : ((1 : ℚ⟦X⟧) + (-6 * X : ℚ⟦X⟧) * G + (9 * X ^ 2 : ℚ⟦X⟧) * G ^ 2) ^ 1 * ((X - 9 * X ^ 2) * derivative ℚ G + (1 - 6 * X) * G - (1)) = 0 := by
    linear_combination ((1 : ℚ⟦X⟧)) * hP +
      ((X - 9 * X ^ 2 : ℚ⟦X⟧)) * hd1
  have hPG : (1 : ℚ⟦X⟧) + (-6 * X : ℚ⟦X⟧) * G + (9 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 1 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-3 * X : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ G * X * C 1 + derivative ℚ G * X * X * C (-9) +
      G * C 1 + G * X * C (-6) =
      C 1 := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-3 * X : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    1 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-9) * ((m : ℚ) + 1) * coeff (m + 1) G +
      1 * coeff (m + 1 + 1) G + (-6) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-3 * X : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    1 * coeff (0 + 1) G + 1 * coeff (0 + 1) G +
      (-6) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A097188Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a097188.main := by
  intro G hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : m + 1 - 1 = m := rfl
  rw [e1]
  have hP : (-1 : PowerSeries ℚ) + (1 : PowerSeries ℚ) * G + (-3 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (3 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3 = 0 := by
    linear_combination hG
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A097188Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    have r := A097188Aux.rel G hP h0c m
    push_cast
    linear_combination r
