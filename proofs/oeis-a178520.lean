import OMAStatements.S_oeis_a178520

-- Problem: A178520: Number of ordered trees with n edges and with no vertex of outdegree 2 that have two leaves as their two children.
-- Upstream: formal-conjectures statements/oeis-a178520.lean:0 (declaration OMA.S_oeis_a178520.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A178520Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-1 + X ^ 2 : ℚ⟦X⟧) + (1 - X ^ 3 : ℚ⟦X⟧) * G + (-X : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (X + X ^ 2 + X ^ 3 - 82 * X ^ 4 + 10 * X ^ 5 + 42 * X ^ 6 + X ^ 7 + 5 * X ^ 8 + 21 * X ^ 9) * derivative ℚ G + (1 + 3 * X + 11 * X ^ 2 - 43 * X ^ 3 - 5 * X ^ 4 - 21 * X ^ 5 - 2 * X ^ 6 - 10 * X ^ 7 - 42 * X ^ 8) * G =
      1 + 5 * X + 18 * X ^ 2 - 10 * X ^ 3 - 38 * X ^ 4 + 102 * X ^ 5 - 15 * X ^ 6 - 63 * X ^ 7 := by
  have hp0 : (-1 + 1 * (X * X) : ℚ⟦X⟧) + (1 - 1 * (X * X * X) : ℚ⟦X⟧) * G + (-1 * X : ℚ⟦X⟧) * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 + 1 * (X * X) : ℚ⟦X⟧) + (1 - 1 * (X * X * X) : ℚ⟦X⟧) * G + (-1 * X : ℚ⟦X⟧) * G * G) =
      (2 * X : ℚ⟦X⟧) + (1 - X ^ 3 : ℚ⟦X⟧) * (derivative ℚ G) + (-3 * X ^ 2 : ℚ⟦X⟧) * G + (-2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz]
    ring
  have hd1 : (2 * X : ℚ⟦X⟧) + (1 - X ^ 3 : ℚ⟦X⟧) * (derivative ℚ G) + (-3 * X ^ 2 : ℚ⟦X⟧) * G + (-2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL1, hp0, map_zero]
  have hfull : ((1 - X ^ 3 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * G) ^ 1 * ((X + X ^ 2 + X ^ 3 - 82 * X ^ 4 + 10 * X ^ 5 + 42 * X ^ 6 + X ^ 7 + 5 * X ^ 8 + 21 * X ^ 9) * derivative ℚ G + (1 + 3 * X + 11 * X ^ 2 - 43 * X ^ 3 - 5 * X ^ 4 - 21 * X ^ 5 - 2 * X ^ 6 - 10 * X ^ 7 - 42 * X ^ 8) * G - (1 + 5 * X + 18 * X ^ 2 - 10 * X ^ 3 - 38 * X ^ 4 + 102 * X ^ 5 - 15 * X ^ 6 - 63 * X ^ 7)) = 0 := by
    linear_combination ((1 + 5 * X + 21 * X ^ 2 - 4 * X ^ 3 - 20 * X ^ 4 - 84 * X ^ 5 - 5 * X ^ 6 - 25 * X ^ 7 - 105 * X ^ 8 : ℚ⟦X⟧)) * hP +
      ((X + X ^ 2 + X ^ 3 - 82 * X ^ 4 + 10 * X ^ 5 + 42 * X ^ 6 + X ^ 7 + 5 * X ^ 8 + 21 * X ^ 9 : ℚ⟦X⟧)) * hd1
  have hPG : (1 - X ^ 3 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * G ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 1 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-1 + X ^ 2 : ℚ⟦X⟧) + (1 - X ^ 3 : ℚ⟦X⟧) * G + (-X : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ G * X * C 1 + derivative ℚ G * X * X * C 1 +
      derivative ℚ G * X * X * X * C 1 + derivative ℚ G * X * X * X * X * C (-82) +
      derivative ℚ G * X * X * X * X * X * C 10 + derivative ℚ G * X * X * X * X * X * X * C 42 +
      derivative ℚ G * X * X * X * X * X * X * X * C 1 + derivative ℚ G * X * X * X * X * X * X * X * X * C 5 +
      derivative ℚ G * X * X * X * X * X * X * X * X * X * C 21 + G * C 1 +
      G * X * C 3 + G * X * X * C 11 +
      G * X * X * X * C (-43) + G * X * X * X * X * C (-5) +
      G * X * X * X * X * X * C (-21) + G * X * X * X * X * X * X * C (-2) +
      G * X * X * X * X * X * X * X * C (-10) + G * X * X * X * X * X * X * X * X * C (-42) =
      C 1 + C 5 * X +
      C 18 * X * X + C (-10) * X * X * X +
      C (-38) * X * X * X * X + C 102 * X * X * X * X * X +
      C (-15) * X * X * X * X * X * X + C (-63) * X * X * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-1 + X ^ 2 : ℚ⟦X⟧) + (1 - X ^ 3 : ℚ⟦X⟧) * G + (-X : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    1 * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 1 * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      1 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-82) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      10 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 42 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      1 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 5 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      21 * ((m : ℚ) + 1) * coeff (m + 1) G + 1 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      3 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 11 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-43) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-21) * coeff (m + 1 + 1 + 1 + 1) G + (-2) * coeff (m + 1 + 1 + 1) G +
      (-10) * coeff (m + 1 + 1) G + (-42) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-1 + X ^ 2 : ℚ⟦X⟧) + (1 - X ^ 3 : ℚ⟦X⟧) * G + (-X : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    8 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 7 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      6 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-410) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      40 * coeff (0 + 1 + 1 + 1 + 1) G + 126 * coeff (0 + 1 + 1 + 1) G +
      2 * coeff (0 + 1 + 1) G + 5 * coeff (0 + 1) G +
      1 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 3 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      11 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-43) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-5) * coeff (0 + 1 + 1 + 1 + 1) G + (-21) * coeff (0 + 1 + 1 + 1) G +
      (-2) * coeff (0 + 1 + 1) G + (-10) * coeff (0 + 1) G +
      (-42) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A178520Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a178520.main := by
  intro G hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 8, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m + 1 := rfl
  have e8 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 8 = m := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  have hP : (-1 + PowerSeries.X ^ 2 : PowerSeries ℚ) + (1 - PowerSeries.X ^ 3 : PowerSeries ℚ) * G + (-PowerSeries.X : PowerSeries ℚ) * G ^ 2 = 0 := by
    linear_combination hG
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A178520Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    have r := A178520Aux.rel G hP h0c m
    push_cast
    linear_combination r
