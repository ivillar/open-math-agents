import OMAStatements.S_oeis_a097192

-- Problem: A097192: Main diagonal of triangle A097190, in which the n-th row polynomial R_n(y) is formed from the initial (n+1) terms of g.f. A097191(y)^(n+1), where R_n(1/3) = 9^n for all n>=0.
-- Upstream: formal-conjectures statements/oeis-a097192.lean:0 (declaration OMA.S_oeis_a097192.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A097192Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 - 216 * X + 20412 * X ^ 2 - 1102248 * X ^ 3 + 37200870 * X ^ 4 - 803538792 * X ^ 5 + 10847773692 * X ^ 6 - 83682825624 * X ^ 7 + 282429536481 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (X - 27 * X ^ 2) * derivative ℚ G + (-24 * X) * G =
      0 := by
  have d216 : derivative ℚ (216 : ℚ⟦X⟧) = 0 := dnum 216
  have d20412 : derivative ℚ (20412 : ℚ⟦X⟧) = 0 := dnum 20412
  have d1102248 : derivative ℚ (1102248 : ℚ⟦X⟧) = 0 := dnum 1102248
  have d37200870 : derivative ℚ (37200870 : ℚ⟦X⟧) = 0 := dnum 37200870
  have d803538792 : derivative ℚ (803538792 : ℚ⟦X⟧) = 0 := dnum 803538792
  have d10847773692 : derivative ℚ (10847773692 : ℚ⟦X⟧) = 0 := dnum 10847773692
  have d83682825624 : derivative ℚ (83682825624 : ℚ⟦X⟧) = 0 := dnum 83682825624
  have d282429536481 : derivative ℚ (282429536481 : ℚ⟦X⟧) = 0 := dnum 282429536481
  have hp0 : (-1 : ℚ⟦X⟧) + (1 - 216 * X + 20412 * (X * X) - 1102248 * (X * X * X) + 37200870 * (X * X * X * X) - 803538792 * (X * X * X * X * X) + 10847773692 * (X * X * X * X * X * X) - 83682825624 * (X * X * X * X * X * X * X) + 282429536481 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * G * G * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 : ℚ⟦X⟧) + (1 - 216 * X + 20412 * (X * X) - 1102248 * (X * X * X) + 37200870 * (X * X * X * X) - 803538792 * (X * X * X * X * X) + 10847773692 * (X * X * X * X * X * X) - 83682825624 * (X * X * X * X * X * X * X) + 282429536481 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * G * G * G * G * G * G) =
      (9 - 1944 * X + 183708 * X ^ 2 - 9920232 * X ^ 3 + 334807830 * X ^ 4 - 7231849128 * X ^ 5 + 97629963228 * X ^ 6 - 753145430616 * X ^ 7 + 2541865828329 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (-216 + 40824 * X - 3306744 * X ^ 2 + 148803480 * X ^ 3 - 4017693960 * X ^ 4 + 65086642152 * X ^ 5 - 585779779368 * X ^ 6 + 2259436291848 * X ^ 7 : ℚ⟦X⟧) * G ^ 9 := by
    simp [Derivation.leibniz, d216, d20412, d1102248, d37200870, d803538792, d10847773692, d83682825624, d282429536481]
    ring
  have hd1 : (9 - 1944 * X + 183708 * X ^ 2 - 9920232 * X ^ 3 + 334807830 * X ^ 4 - 7231849128 * X ^ 5 + 97629963228 * X ^ 6 - 753145430616 * X ^ 7 + 2541865828329 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (-216 + 40824 * X - 3306744 * X ^ 2 + 148803480 * X ^ 3 - 4017693960 * X ^ 4 + 65086642152 * X ^ 5 - 585779779368 * X ^ 6 + 2259436291848 * X ^ 7 : ℚ⟦X⟧) * G ^ 9 = 0 := by rw [← hL1, hp0, map_zero]
  have hfull : ((9 - 1944 * X + 183708 * X ^ 2 - 9920232 * X ^ 3 + 334807830 * X ^ 4 - 7231849128 * X ^ 5 + 97629963228 * X ^ 6 - 753145430616 * X ^ 7 + 2541865828329 * X ^ 8 : ℚ⟦X⟧) * G ^ 8) ^ 1 * ((X - 27 * X ^ 2) * derivative ℚ G + (-24 * X) * G - (0)) = 0 := by
    linear_combination ((0 : ℚ⟦X⟧)) * hP +
      ((X - 27 * X ^ 2 : ℚ⟦X⟧)) * hd1
  have k9 : constantCoeff (9 : ℚ⟦X⟧) = 9 := cnum 9
  have hPG : (9 - 1944 * X + 183708 * X ^ 2 - 9920232 * X ^ 3 + 334807830 * X ^ 4 - 7231849128 * X ^ 5 + 97629963228 * X ^ 6 - 753145430616 * X ^ 7 + 2541865828329 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k9] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 1 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 - 216 * X + 20412 * X ^ 2 - 1102248 * X ^ 3 + 37200870 * X ^ 4 - 803538792 * X ^ 5 + 10847773692 * X ^ 6 - 83682825624 * X ^ 7 + 282429536481 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ G * X * C 1 + derivative ℚ G * X * X * C (-27) +
      G * X * C (-24) =
      0 := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 - 216 * X + 20412 * X ^ 2 - 1102248 * X ^ 3 + 37200870 * X ^ 4 - 803538792 * X ^ 5 + 10847773692 * X ^ 6 - 83682825624 * X ^ 7 + 282429536481 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    1 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-27) * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-24) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 - 216 * X + 20412 * X ^ 2 - 1102248 * X ^ 3 + 37200870 * X ^ 4 - 803538792 * X ^ 5 + 10847773692 * X ^ 6 - 83682825624 * X ^ 7 + 282429536481 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    1 * coeff (0 + 1) G + (-24) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A097192Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a097192.main := by
  intro G h0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : m + 1 - 1 = m := rfl
  rw [e1]
  have hP : (-1 : PowerSeries ℚ) + (1 - 216 * PowerSeries.X + 20412 * PowerSeries.X ^ 2 - 1102248 * PowerSeries.X ^ 3 + 37200870 * PowerSeries.X ^ 4 - 803538792 * PowerSeries.X ^ 5 + 10847773692 * PowerSeries.X ^ 6 - 83682825624 * PowerSeries.X ^ 7 + 282429536481 * PowerSeries.X ^ 8 : PowerSeries ℚ) * G ^ 9 = 0 := by
    linear_combination hG
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A097192Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    have r := A097192Aux.rel G hP h0c m
    push_cast
    linear_combination r
