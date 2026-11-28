import OMAStatements.S_oeis_a171847

-- Problem: A171847: Total area under all peakless Motzkin paths of length n (n>=0).
-- Upstream: formal-conjectures statements/oeis-a171847.lean:0 (declaration OMA.S_oeis_a171847.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A171847Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (2 * X ^ 3 - X ^ 4 + 2 * X ^ 5 : ℚ⟦X⟧) + (-1 + 4 * X - 4 * X ^ 2 + 4 * X ^ 3 - 7 * X ^ 4 - 6 * X ^ 6 + X ^ 8 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 + 11 * X ^ 6 + 2 * X ^ 8 - 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (X - 5 * X ^ 2 + 7 * X ^ 3 - 6 * X ^ 4 + 13 * X ^ 5 - 11 * X ^ 6 + 13 * X ^ 7 - 6 * X ^ 8 + 7 * X ^ 9 - 5 * X ^ 10 + X ^ 11) * derivative ℚ G + (2 - 10 * X + 10 * X ^ 2 - 4 * X ^ 3 + 34 * X ^ 4 - 22 * X ^ 5 + 18 * X ^ 6 - 20 * X ^ 7 + 18 * X ^ 8 - 10 * X ^ 9 + 2 * X ^ 10) * G =
      10 * X ^ 3 - 8 * X ^ 4 + 6 * X ^ 5 - 4 * X ^ 6 + 2 * X ^ 7 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have d11 : derivative ℚ (11 : ℚ⟦X⟧) = 0 := dnum 11
  have hp0 : (2 * (X * X * X) - 1 * (X * X * X * X) + 2 * (X * X * X * X * X) : ℚ⟦X⟧) + (-1 + 4 * X - 4 * (X * X) + 4 * (X * X * X) - 7 * (X * X * X * X) - 6 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * (X * X) - 4 * (X * X * X) + 2 * (X * X * X * X) + 11 * (X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((2 * (X * X * X) - 1 * (X * X * X * X) + 2 * (X * X * X * X * X) : ℚ⟦X⟧) + (-1 + 4 * X - 4 * (X * X) + 4 * (X * X * X) - 7 * (X * X * X * X) - 6 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * (X * X) - 4 * (X * X * X) + 2 * (X * X * X * X) + 11 * (X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X) - 4 * (X * X * X * X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (6 * X ^ 2 - 4 * X ^ 3 + 10 * X ^ 4 : ℚ⟦X⟧) + (-1 + 4 * X - 4 * X ^ 2 + 4 * X ^ 3 - 7 * X ^ 4 - 6 * X ^ 6 + X ^ 8 : ℚ⟦X⟧) * (derivative ℚ G) + (4 - 8 * X + 12 * X ^ 2 - 28 * X ^ 3 - 36 * X ^ 5 + 8 * X ^ 7 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 + 22 * X ^ 6 + 4 * X ^ 8 - 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 12 * X ^ 2 + 8 * X ^ 3 + 66 * X ^ 5 + 16 * X ^ 7 - 36 * X ^ 8 + 10 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d4, d6, d7, d11]
    ring
  have hd1 : (6 * X ^ 2 - 4 * X ^ 3 + 10 * X ^ 4 : ℚ⟦X⟧) + (-1 + 4 * X - 4 * X ^ 2 + 4 * X ^ 3 - 7 * X ^ 4 - 6 * X ^ 6 + X ^ 8 : ℚ⟦X⟧) * (derivative ℚ G) + (4 - 8 * X + 12 * X ^ 2 - 28 * X ^ 3 - 36 * X ^ 5 + 8 * X ^ 7 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 + 22 * X ^ 6 + 4 * X ^ 8 - 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 12 * X ^ 2 + 8 * X ^ 3 + 66 * X ^ 5 + 16 * X ^ 7 - 36 * X ^ 8 + 10 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL1, hp0, map_zero]
  have hfull : ((-1 + 4 * X - 4 * X ^ 2 + 4 * X ^ 3 - 7 * X ^ 4 - 6 * X ^ 6 + X ^ 8 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 + 22 * X ^ 6 + 4 * X ^ 8 - 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G) ^ 1 * ((X - 5 * X ^ 2 + 7 * X ^ 3 - 6 * X ^ 4 + 13 * X ^ 5 - 11 * X ^ 6 + 13 * X ^ 7 - 6 * X ^ 8 + 7 * X ^ 9 - 5 * X ^ 10 + X ^ 11) * derivative ℚ G + (2 - 10 * X + 10 * X ^ 2 - 4 * X ^ 3 + 34 * X ^ 4 - 22 * X ^ 5 + 18 * X ^ 6 - 20 * X ^ 7 + 18 * X ^ 8 - 10 * X ^ 9 + 2 * X ^ 10) * G - (10 * X ^ 3 - 8 * X ^ 4 + 6 * X ^ 5 - 4 * X ^ 6 + 2 * X ^ 7)) = 0 := by
    linear_combination ((2 - 6 * X - 2 * X ^ 2 + 12 * X ^ 3 - 6 * X ^ 4 + 22 * X ^ 5 - 46 * X ^ 6 + 12 * X ^ 7 - 26 * X ^ 8 + 26 * X ^ 9 - 6 * X ^ 10 : ℚ⟦X⟧)) * hP +
      ((X - 5 * X ^ 2 + 7 * X ^ 3 - 6 * X ^ 4 + 13 * X ^ 5 - 11 * X ^ 6 + 13 * X ^ 7 - 6 * X ^ 8 + 7 * X ^ 9 - 5 * X ^ 10 + X ^ 11 : ℚ⟦X⟧)) * hd1
  have hPG : (-1 + 4 * X - 4 * X ^ 2 + 4 * X ^ 3 - 7 * X ^ 4 - 6 * X ^ 6 + X ^ 8 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4 + 22 * X ^ 6 + 4 * X ^ 8 - 8 * X ^ 9 + 2 * X ^ 10 : ℚ⟦X⟧) * G ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 1 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (2 * X ^ 3 - X ^ 4 + 2 * X ^ 5 : ℚ⟦X⟧) + (-1 + 4 * X - 4 * X ^ 2 + 4 * X ^ 3 - 7 * X ^ 4 - 6 * X ^ 6 + X ^ 8 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 + 11 * X ^ 6 + 2 * X ^ 8 - 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ G * X * C 1 + derivative ℚ G * X * X * C (-5) +
      derivative ℚ G * X * X * X * C 7 + derivative ℚ G * X * X * X * X * C (-6) +
      derivative ℚ G * X * X * X * X * X * C 13 + derivative ℚ G * X * X * X * X * X * X * C (-11) +
      derivative ℚ G * X * X * X * X * X * X * X * C 13 + derivative ℚ G * X * X * X * X * X * X * X * X * C (-6) +
      derivative ℚ G * X * X * X * X * X * X * X * X * X * C 7 + derivative ℚ G * X * X * X * X * X * X * X * X * X * X * C (-5) +
      derivative ℚ G * X * X * X * X * X * X * X * X * X * X * X * C 1 + G * C 2 +
      G * X * C (-10) + G * X * X * C 10 +
      G * X * X * X * C (-4) + G * X * X * X * X * C 34 +
      G * X * X * X * X * X * C (-22) + G * X * X * X * X * X * X * C 18 +
      G * X * X * X * X * X * X * X * C (-20) + G * X * X * X * X * X * X * X * X * C 18 +
      G * X * X * X * X * X * X * X * X * X * C (-10) + G * X * X * X * X * X * X * X * X * X * X * C 2 =
      C 10 * X * X * X + C (-8) * X * X * X * X +
      C 6 * X * X * X * X * X + C (-4) * X * X * X * X * X * X +
      C 2 * X * X * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (2 * X ^ 3 - X ^ 4 + 2 * X ^ 5 : ℚ⟦X⟧) + (-1 + 4 * X - 4 * X ^ 2 + 4 * X ^ 3 - 7 * X ^ 4 - 6 * X ^ 6 + X ^ 8 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 + 11 * X ^ 6 + 2 * X ^ 8 - 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    1 * ((m : ℚ) + 11) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-5) * ((m : ℚ) + 10) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      7 * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-6) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      13 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-11) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      13 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-6) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      7 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-5) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      1 * ((m : ℚ) + 1) * coeff (m + 1) G + 2 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-10) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 10 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 34 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-22) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 18 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-20) * coeff (m + 1 + 1 + 1 + 1) G + 18 * coeff (m + 1 + 1 + 1) G +
      (-10) * coeff (m + 1 + 1) G + 2 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (2 * X ^ 3 - X ^ 4 + 2 * X ^ 5 : ℚ⟦X⟧) + (-1 + 4 * X - 4 * X ^ 2 + 4 * X ^ 3 - 7 * X ^ 4 - 6 * X ^ 6 + X ^ 8 : ℚ⟦X⟧) * G + (X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 + 11 * X ^ 6 + 2 * X ^ 8 - 4 * X ^ 9 + X ^ 10 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    10 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-45) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      56 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-42) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      78 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-55) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      52 * coeff (0 + 1 + 1 + 1 + 1) G + (-18) * coeff (0 + 1 + 1 + 1) G +
      14 * coeff (0 + 1 + 1) G + (-5) * coeff (0 + 1) G +
      2 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-10) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      10 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-4) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      34 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-22) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      18 * coeff (0 + 1 + 1 + 1 + 1) G + (-20) * coeff (0 + 1 + 1 + 1) G +
      18 * coeff (0 + 1 + 1) G + (-10) * coeff (0 + 1) G +
      2 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A171847Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a171847.main := by
  intro T G hT hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 10, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 + 1 + 1 + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m + 1 + 1 + 1 := rfl
  have e8 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 8 = m + 1 + 1 := rfl
  have e9 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 9 = m + 1 := rfl
  have e10 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 10 = m := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  have kn2 : PowerSeries.constantCoeff (2 : PowerSeries ℚ) = 2 := A171847Aux.cnum 2
  have hN1 : ((1) + (-2) * PowerSeries.X + (-1) * PowerSeries.X ^ 2 + (-2) * PowerSeries.X ^ 3 + (1) * PowerSeries.X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [kn2] at h'
  have hM : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 6) * (((1) + (-2) * PowerSeries.X + (-1) * PowerSeries.X ^ 2 + (-2) * PowerSeries.X ^ 3 + (1) * PowerSeries.X ^ 4) ^ 2 * ((2 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 5 : PowerSeries ℚ) + (-1 + 4 * PowerSeries.X - 4 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 - 7 * PowerSeries.X ^ 4 - 6 * PowerSeries.X ^ 6 + PowerSeries.X ^ 8 : PowerSeries ℚ) * G + (PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 + 11 * PowerSeries.X ^ 6 + 2 * PowerSeries.X ^ 8 - 4 * PowerSeries.X ^ 9 + PowerSeries.X ^ 10 : PowerSeries ℚ) * G ^ 2)) = 0 := by
    linear_combination ((1) * PowerSeries.X ^ 8 + (1) * PowerSeries.X ^ 8 * T + (-4) * PowerSeries.X ^ 9 + (-5) * PowerSeries.X ^ 9 * T + (2) * PowerSeries.X ^ 10 + (7) * PowerSeries.X ^ 10 * T + (1) * PowerSeries.X ^ 10 * T ^ 2 + (-6) * PowerSeries.X ^ 11 * T + (-4) * PowerSeries.X ^ 11 * T ^ 2 + (11) * PowerSeries.X ^ 12 + (13) * PowerSeries.X ^ 12 * T + (2) * PowerSeries.X ^ 12 * T ^ 2 + (-11) * PowerSeries.X ^ 13 * T + (2) * PowerSeries.X ^ 14 + (13) * PowerSeries.X ^ 14 * T + (11) * PowerSeries.X ^ 14 * T ^ 2 + (-4) * PowerSeries.X ^ 15 + (-6) * PowerSeries.X ^ 15 * T + (1) * PowerSeries.X ^ 16 + (7) * PowerSeries.X ^ 16 * T + (2) * PowerSeries.X ^ 16 * T ^ 2 + (-5) * PowerSeries.X ^ 17 * T + (-4) * PowerSeries.X ^ 17 * T ^ 2 + (1) * PowerSeries.X ^ 18 * T + (1) * PowerSeries.X ^ 18 * T ^ 2) * hT +
      ((1) * PowerSeries.X ^ 6 + (-6) * PowerSeries.X ^ 7 + (11) * PowerSeries.X ^ 8 + (-1) * PowerSeries.X ^ 8 * G + (-10) * PowerSeries.X ^ 9 + (6) * PowerSeries.X ^ 9 * G + (21) * PowerSeries.X ^ 10 + (-1) * PowerSeries.X ^ 10 * T ^ 2 + (-9) * PowerSeries.X ^ 10 * G + (-26) * PowerSeries.X ^ 11 + (4) * PowerSeries.X ^ 11 * T ^ 2 + (2) * PowerSeries.X ^ 11 * G + (13) * PowerSeries.X ^ 12 + (-2) * PowerSeries.X ^ 12 * T ^ 2 + (-18) * PowerSeries.X ^ 12 * G + (-30) * PowerSeries.X ^ 13 + (30) * PowerSeries.X ^ 13 * G + (11) * PowerSeries.X ^ 14 + (-11) * PowerSeries.X ^ 14 * T ^ 2 + (7) * PowerSeries.X ^ 14 * G + (-10) * PowerSeries.X ^ 15 + (30) * PowerSeries.X ^ 15 * G + (9) * PowerSeries.X ^ 16 + (-2) * PowerSeries.X ^ 16 * T ^ 2 + (-18) * PowerSeries.X ^ 16 * G + (-2) * PowerSeries.X ^ 17 + (4) * PowerSeries.X ^ 17 * T ^ 2 + (2) * PowerSeries.X ^ 17 * G + (-1) * PowerSeries.X ^ 18 * T ^ 2 + (-9) * PowerSeries.X ^ 18 * G + (6) * PowerSeries.X ^ 19 * G + (-1) * PowerSeries.X ^ 20 * G) * hG
  have hLne : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 6) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 6 PowerSeries.X_ne_zero)
  have hP : (2 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 5 : PowerSeries ℚ) + (-1 + 4 * PowerSeries.X - 4 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 - 7 * PowerSeries.X ^ 4 - 6 * PowerSeries.X ^ 6 + PowerSeries.X ^ 8 : PowerSeries ℚ) * G + (PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 + 11 * PowerSeries.X ^ 6 + 2 * PowerSeries.X ^ 8 - 4 * PowerSeries.X ^ 9 + PowerSeries.X ^ 10 : PowerSeries ℚ) * G ^ 2 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 2 hN1)
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A171847Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    have r := A171847Aux.rel G hP h0c m
    push_cast
    linear_combination r
