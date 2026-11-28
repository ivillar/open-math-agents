import OMAStatements.S_oeis_a189176

-- Problem: A189176: Row sums of the Riordan matrix (1+x/sqrt(1-4*x),(1-sqrt(1-4*x))/2) (A189175).
-- Upstream: formal-conjectures statements/oeis-a189176.lean:0 (declaration OMA.S_oeis_a189176.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A189176Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 * X - 8 * X ^ 2 + (0) * S) = 1 - 5 * X + 4 * X ^ 2 + (-1 + 5 * X) * S) :
    (-4 * X + 36 * X ^ 2 - 80 * X ^ 3) * derivative ℚ G + (-4 + 24 * X - 40 * X ^ 2) * G = -4 + 8 * X + 20 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 * X - 8 * X ^ 2) * G = (1 - 5 * X + 4 * X ^ 2 : ℚ⟦X⟧) + (-1 + 5 * X) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 * X - 8 * (X * X) : ℚ⟦X⟧) * G) = (2 - 16 * X) * G + (2 * X - 8 * X ^ 2) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d8]
    ring
  have hR : derivative ℚ ((1 - 5 * X + 4 * (X * X) : ℚ⟦X⟧) + (-1 + 5 * X : ℚ⟦X⟧) * S) =
      -5 + 8 * X + (5) * S + (-1 + 5 * X) * derivative ℚ S := by
    simp [Derivation.leibniz, d4, d5]
    ring
  have hk2 : (2 * X - 8 * (X * X) : ℚ⟦X⟧) * G = (1 - 5 * X + 4 * (X * X) : ℚ⟦X⟧) + (-1 + 5 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (2 - 16 * X) * G + (2 * X - 8 * X ^ 2) * derivative ℚ G =
      -5 + 8 * X + (5) * S + (-1 + 5 * X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 4 * X) * ((-4 * X + 36 * X ^ 2 - 80 * X ^ 3) * derivative ℚ G + (-4 + 24 * X - 40 * X ^ 2) * G - (-4 + 8 * X + 20 * X ^ 2)) = 0 := by
    linear_combination (-1 + 5 * X) ^ 2 * S * hdS - 2 * (-1 + 5 * X) ^ 2 * derivative ℚ S * hS -
      (2 * (5) * (1 - 4 * X) + (-1 + 5 * X) * (-4)) * hk + 2 * (-1 + 5 * X) * (1 - 4 * X) * hdk
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 * X - 8 * X ^ 2 + (0) * S) = 1 - 5 * X + 4 * X ^ 2 + (-1 + 5 * X) * S) :
    derivative ℚ G * X * C (-4) + derivative ℚ G * X * X * C 36 +
      derivative ℚ G * X * X * X * C (-80) + G * C (-4) +
      G * X * C 24 + G * X * X * C (-40) =
      C (-4) + C 8 * X +
      C 20 * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 * X - 8 * X ^ 2 + (0) * S) = 1 - 5 * X + 4 * X ^ 2 + (-1 + 5 * X) * S) (m : ℕ) :
    (-4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 36 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-80) * ((m : ℚ) + 1) * coeff (m + 1) G + (-4) * coeff (m + 1 + 1 + 1) G +
      24 * coeff (m + 1 + 1) G + (-40) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A189176Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a189176.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  rw [e1, e2]
  have r := A189176Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG) m
  push_cast
  linear_combination ((-1 : ℚ) / 4) * r
