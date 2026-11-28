import OMAStatements.S_oeis_a276310

-- Problem: A276310: G.f. A(x) satisfies: x = A(x)-2*A(x)^2-2*A(x)^3.
-- Upstream: formal-conjectures statements/oeis-a276310.lean:0 (declaration OMA.S_oeis_a276310.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A276310Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-2 : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (3 * X ^ 2 - 26 * X ^ 3 - 27 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-13 * X ^ 2 - 27 * X ^ 3) * derivative ℚ G + (3 * X ^ 2) * G =
      -X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have hp0 : (-1 * X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-2 : ℚ⟦X⟧) * G * G + (-2 : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 * X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-2 : ℚ⟦X⟧) * G * G + (-2 : ℚ⟦X⟧) * G * G * G) =
      (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2]
    ring
  have hd1 : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * G * (derivative ℚ G) = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * G * (derivative ℚ G)) =
      (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-4 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d4, d6]
    ring
  have hd2 : (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-4 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((1 : ℚ⟦X⟧) + (-4 : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((3 * X ^ 2 - 26 * X ^ 3 - 27 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-13 * X ^ 2 - 27 * X ^ 3) * derivative ℚ G + (3 * X ^ 2) * G - (-X ^ 2)) = 0 := by
    linear_combination ((131 * X ^ 2 + 108 * X ^ 3 : ℚ⟦X⟧) + (204 * X ^ 2 + 324 * X ^ 3 : ℚ⟦X⟧) * G + (216 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (432 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 + (324 * X ^ 2 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((-X ^ 2 - 131 * X ^ 3 - 108 * X ^ 4 : ℚ⟦X⟧) + (12 * X ^ 2 - 104 * X ^ 3 - 108 * X ^ 4 : ℚ⟦X⟧) * (derivative ℚ G) + (140 * X ^ 2 - 96 * X ^ 3 - 324 * X ^ 4 : ℚ⟦X⟧) * G + (-12 * X ^ 2 + 104 * X ^ 3 + 108 * X ^ 4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-52 * X ^ 2 - 108 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 + (-216 * X ^ 2 + 1872 * X ^ 3 + 1944 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-624 * X ^ 2 - 1296 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 + (-216 * X ^ 2 + 1872 * X ^ 3 + 1944 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-468 * X ^ 2 - 972 * X ^ 3 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((3 * X ^ 2 - 26 * X ^ 3 - 27 * X ^ 4 : ℚ⟦X⟧) + (-24 * X ^ 2 + 208 * X ^ 3 + 216 * X ^ 4 : ℚ⟦X⟧) * G + (12 * X ^ 2 - 104 * X ^ 3 - 108 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (144 * X ^ 2 - 1248 * X ^ 3 - 1296 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 + (108 * X ^ 2 - 936 * X ^ 3 - 972 * X ^ 4 : ℚ⟦X⟧) * G ^ 4) * hd2
  have k4 : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
  have k6 : constantCoeff (6 : ℚ⟦X⟧) = 6 := cnum 6
  have hPG : (1 : ℚ⟦X⟧) + (-4 : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k4, k6] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-2 : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 3 + derivative ℚ (derivative ℚ G) * X * X * X * C (-26) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-27) + derivative ℚ G * X * X * C (-13) +
      derivative ℚ G * X * X * X * C (-27) + G * X * X * C 3 =
      C (-1) * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-2 : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    3 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-26) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-27) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-13) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-27) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 3 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-2 : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    18 * coeff (0 + 1 + 1 + 1) G + (-52) * coeff (0 + 1 + 1) G +
      (-26) * coeff (0 + 1 + 1) G + (-27) * coeff (0 + 1) G +
      3 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A276310Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a276310.main := by
  intro G h0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  rw [e1, e2]
  have hP : (-PowerSeries.X : PowerSeries ℚ) + (1 : PowerSeries ℚ) * G + (-2 : PowerSeries ℚ) * G ^ 2 + (-2 : PowerSeries ℚ) * G ^ 3 = 0 := by
    linear_combination -hG
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A276310Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    have r := A276310Aux.rel G hP h0c m
    push_cast
    linear_combination r
