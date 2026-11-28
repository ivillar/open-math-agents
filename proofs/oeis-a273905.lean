import OMAStatements.S_oeis_a273905

-- Problem: A273905: Number of symmetric bargraphs having semiperimeter n (n>=2).
-- Upstream: formal-conjectures statements/oeis-a273905.lean:0 (declaration OMA.S_oeis_a273905.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A273905Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2 + 2 * X ^ 4 + X ^ 8)
    (hG : G * (2 * X - 2 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + (0) * S) = -1 - X + 2 * X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + X ^ 5 + (1 + X) * S) :
    (4 * X - 16 * X ^ 3 + 8 * X ^ 5 + 4 * X ^ 9) * derivative ℚ G + (4 - 8 * X - 8 * X ^ 2 - 16 * X ^ 4 + 24 * X ^ 5 - 8 * X ^ 6 - 4 * X ^ 8) * G = 12 * X ^ 2 + 24 * X ^ 3 + 4 * X ^ 4 - 16 * X ^ 5 - 4 * X ^ 6 + 8 * X ^ 7 + 4 * X ^ 8 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hS2 : S * S = (1 - 4 * (X * X) + 2 * (X * X * X * X) + 1 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 * X - 2 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4) * G = (-1 - X + 2 * X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + X ^ 5 : ℚ⟦X⟧) + (1 + X) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * (X * X) + 2 * (X * X * X * X) + 1 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) = -8 * X + 8 * X ^ 3 + 8 * X ^ 7 := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 * X + 8 * X ^ 3 + 8 * X ^ 7 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 * X - 2 * (X * X) - 2 * (X * X * X) - 2 * (X * X * X * X) : ℚ⟦X⟧) * G) = (2 - 4 * X - 6 * X ^ 2 - 8 * X ^ 3) * G + (2 * X - 2 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d2]
    ring
  have hR : derivative ℚ ((-1 - 1 * X + 2 * (X * X) + 4 * (X * X * X) + 3 * (X * X * X * X) + 1 * (X * X * X * X * X) : ℚ⟦X⟧) + (1 + 1 * X : ℚ⟦X⟧) * S) =
      -1 + 4 * X + 12 * X ^ 2 + 12 * X ^ 3 + 5 * X ^ 4 + (1) * S + (1 + X) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d3, d4]
    ring
  have hk2 : (2 * X - 2 * (X * X) - 2 * (X * X * X) - 2 * (X * X * X * X) : ℚ⟦X⟧) * G = (-1 - 1 * X + 2 * (X * X) + 4 * (X * X * X) + 3 * (X * X * X * X) + 1 * (X * X * X * X * X) : ℚ⟦X⟧) + (1 + 1 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (2 - 4 * X - 6 * X ^ 2 - 8 * X ^ 3) * G + (2 * X - 2 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4) * derivative ℚ G =
      -1 + 4 * X + 12 * X ^ 2 + 12 * X ^ 3 + 5 * X ^ 4 + (1) * S + (1 + X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 2 * X ^ 2 - 2 * X ^ 3 - X ^ 4) * ((4 * X - 16 * X ^ 3 + 8 * X ^ 5 + 4 * X ^ 9) * derivative ℚ G + (4 - 8 * X - 8 * X ^ 2 - 16 * X ^ 4 + 24 * X ^ 5 - 8 * X ^ 6 - 4 * X ^ 8) * G - (12 * X ^ 2 + 24 * X ^ 3 + 4 * X ^ 4 - 16 * X ^ 5 - 4 * X ^ 6 + 8 * X ^ 7 + 4 * X ^ 8)) = 0 := by
    linear_combination (1 + X) ^ 2 * S * hdS - 2 * (1 + X) ^ 2 * derivative ℚ S * hS -
      (2 * (1) * (1 - 4 * X ^ 2 + 2 * X ^ 4 + X ^ 8) + (1 + X) * (-8 * X + 8 * X ^ 3 + 8 * X ^ 7)) * hk + 2 * (1 + X) * (1 - 4 * X ^ 2 + 2 * X ^ 4 + X ^ 8) * hdk
  have hg : (1 - 2 * X ^ 2 - 2 * X ^ 3 - X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2 + 2 * X ^ 4 + X ^ 8)
    (hG : G * (2 * X - 2 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + (0) * S) = -1 - X + 2 * X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + X ^ 5 + (1 + X) * S) :
    derivative ℚ G * X * C 4 + derivative ℚ G * X * X * X * C (-16) +
      derivative ℚ G * X * X * X * X * X * C 8 + derivative ℚ G * X * X * X * X * X * X * X * X * X * C 4 +
      G * C 4 + G * X * C (-8) +
      G * X * X * C (-8) + G * X * X * X * X * C (-16) +
      G * X * X * X * X * X * C 24 + G * X * X * X * X * X * X * C (-8) +
      G * X * X * X * X * X * X * X * X * C (-4) =
      C 12 * X * X + C 24 * X * X * X +
      C 4 * X * X * X * X + C (-16) * X * X * X * X * X +
      C (-4) * X * X * X * X * X * X + C 8 * X * X * X * X * X * X * X +
      C 4 * X * X * X * X * X * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2 + 2 * X ^ 4 + X ^ 8)
    (hG : G * (2 * X - 2 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + (0) * S) = -1 - X + 2 * X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + X ^ 5 + (1 + X) * S) (m : ℕ) :
    4 * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-16) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      8 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 4 * ((m : ℚ) + 1) * coeff (m + 1) G +
      4 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-16) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      24 * coeff (m + 1 + 1 + 1 + 1) G + (-8) * coeff (m + 1 + 1 + 1) G +
      (-4) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A273905Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a273905.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 9, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 + 1 + 1 := rfl
  have e8 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 8 = m + 1 := rfl
  rw [e1, e2, e4, e5, e6, e8]
  have r := A273905Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG) m
  push_cast
  linear_combination ((1 : ℚ) / 4) * r
