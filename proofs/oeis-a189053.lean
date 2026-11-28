import OMAStatements.S_oeis_a189053

-- Problem: A189053: Expansion of d/dx log(1/(1-x/sqrt(1-4*x^2))).
-- Upstream: formal-conjectures statements/oeis-a189053.lean:0 (declaration OMA.S_oeis_a189053.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A189053Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (1 - 8 * X ^ 2 + 16 * X ^ 4 + (-X + 4 * X ^ 3) * S) = 0 + (1) * S) :
    (2 - 26 * X ^ 2 + 112 * X ^ 4 - 160 * X ^ 6) * derivative ℚ G + (-28 * X + 232 * X ^ 3 - 480 * X ^ 5) * G = 2 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d17 : derivative ℚ (17 : ℚ⟦X⟧) = 0 := dnum 17
  have d108 : derivative ℚ (108 : ℚ⟦X⟧) = 0 := dnum 108
  have d304 : derivative ℚ (304 : ℚ⟦X⟧) = 0 := dnum 304
  have d320 : derivative ℚ (320 : ℚ⟦X⟧) = 0 := dnum 320
  have hS2 : S * S = (1 - 4 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (1 - 17 * X ^ 2 + 108 * X ^ 4 - 304 * X ^ 6 + 320 * X ^ 8) * G = (X - 8 * X ^ 3 + 16 * X ^ 5 : ℚ⟦X⟧) + (1 - 8 * X ^ 2 + 16 * X ^ 4) * S := by
    linear_combination (1 - 8 * X ^ 2 + 16 * X ^ 4 - (-X + 4 * X ^ 3) * S) * hG + (-X + 4 * X ^ 3) * ((-X + 4 * X ^ 3) * G - (1)) * hS
  have hPd : derivative ℚ (1 - 4 * (X * X) : ℚ⟦X⟧) = -8 * X := by
    simp [Derivation.leibniz, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((1 - 17 * (X * X) + 108 * (X * X * X * X) - 304 * (X * X * X * X * X * X) + 320 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-34 * X + 432 * X ^ 3 - 1824 * X ^ 5 + 2560 * X ^ 7) * G + (1 - 17 * X ^ 2 + 108 * X ^ 4 - 304 * X ^ 6 + 320 * X ^ 8) * derivative ℚ G := by
    simp [Derivation.leibniz, d17, d108, d304, d320]
    ring
  have hR : derivative ℚ ((1 * X - 8 * (X * X * X) + 16 * (X * X * X * X * X) : ℚ⟦X⟧) + (1 - 8 * (X * X) + 16 * (X * X * X * X) : ℚ⟦X⟧) * S) =
      1 - 24 * X ^ 2 + 80 * X ^ 4 + (-16 * X + 64 * X ^ 3) * S + (1 - 8 * X ^ 2 + 16 * X ^ 4) * derivative ℚ S := by
    simp [Derivation.leibniz, d8, d16]
    ring
  have hk2 : (1 - 17 * (X * X) + 108 * (X * X * X * X) - 304 * (X * X * X * X * X * X) + 320 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (1 * X - 8 * (X * X * X) + 16 * (X * X * X * X * X) : ℚ⟦X⟧) + (1 - 8 * (X * X) + 16 * (X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-34 * X + 432 * X ^ 3 - 1824 * X ^ 5 + 2560 * X ^ 7) * G + (1 - 17 * X ^ 2 + 108 * X ^ 4 - 304 * X ^ 6 + 320 * X ^ 8) * derivative ℚ G =
      1 - 24 * X ^ 2 + 80 * X ^ 4 + (-16 * X + 64 * X ^ 3) * S + (1 - 8 * X ^ 2 + 16 * X ^ 4) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 16 * X ^ 2 + 96 * X ^ 4 - 256 * X ^ 6 + 256 * X ^ 8) * ((2 - 26 * X ^ 2 + 112 * X ^ 4 - 160 * X ^ 6) * derivative ℚ G + (-28 * X + 232 * X ^ 3 - 480 * X ^ 5) * G - (2)) = 0 := by
    linear_combination (1 - 8 * X ^ 2 + 16 * X ^ 4) ^ 2 * S * hdS - 2 * (1 - 8 * X ^ 2 + 16 * X ^ 4) ^ 2 * derivative ℚ S * hS -
      (2 * (-16 * X + 64 * X ^ 3) * (1 - 4 * X ^ 2) + (1 - 8 * X ^ 2 + 16 * X ^ 4) * (-8 * X)) * hk + 2 * (1 - 8 * X ^ 2 + 16 * X ^ 4) * (1 - 4 * X ^ 2) * hdk
  have hg : (1 - 16 * X ^ 2 + 96 * X ^ 4 - 256 * X ^ 6 + 256 * X ^ 8 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (1 - 8 * X ^ 2 + 16 * X ^ 4 + (-X + 4 * X ^ 3) * S) = 0 + (1) * S) :
    derivative ℚ G * C 2 + derivative ℚ G * X * X * C (-26) +
      derivative ℚ G * X * X * X * X * C 112 + derivative ℚ G * X * X * X * X * X * X * C (-160) +
      G * X * C (-28) + G * X * X * X * C 232 +
      G * X * X * X * X * X * C (-480) =
      C 2 := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (1 - 8 * X ^ 2 + 16 * X ^ 4 + (-X + 4 * X ^ 3) * S) = 0 + (1) * S) (m : ℕ) :
    2 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-26) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      112 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-160) * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-28) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 232 * coeff (m + 1 + 1 + 1) G +
      (-480) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (1 - 8 * X ^ 2 + 16 * X ^ 4 + (-X + 4 * X ^ 3) * S) = 0 + (1) * S) :
    12 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-104) * coeff (0 + 1 + 1 + 1 + 1) G +
      224 * coeff (0 + 1 + 1) G + (-28) * coeff (0 + 1 + 1 + 1 + 1) G +
      232 * coeff (0 + 1 + 1) G + (-480) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A189053Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a189053.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 7, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m := rfl
  rw [e1, e2, e3, e4, e5, e6, e7]
  cases m with
  | zero =>
    have r0 := A189053Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) 0
    have r1 := A189053Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast at r0 r1 ⊢
    linear_combination ((1 : ℚ) / 2) * r0 + ((1 : ℚ) / 2) * r1
  | succ m =>
    have r0 := A189053Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) (m + 1)
    have r1 := A189053Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast at r0 r1 ⊢
    linear_combination ((1 : ℚ) / 2) * ((1) * r0 + (1) * r1)
