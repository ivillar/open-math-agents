import OMAStatements.S_oeis_a289684

-- Problem: A289684: Mixing moments for the waiting time in an M/G/1 waiting queue.
-- Upstream: formal-conjectures statements/oeis-a289684.lean:0 (declaration OMA.S_oeis_a289684.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A289684Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-2 + 4 * X + 8 * X ^ 2 + (2) * S) = 4 * X ^ 2 + (0) * S) :
    (256 - 2048 * X + 3072 * X ^ 2 + 4096 * X ^ 3) * derivative ℚ G + (-512 + 6144 * X ^ 2) * G = -512 * X + 3072 * X ^ 2 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-16 * X ^ 2 + 64 * X ^ 3 + 64 * X ^ 4) * G = (-8 * X ^ 2 + 16 * X ^ 3 + 32 * X ^ 4 : ℚ⟦X⟧) + (-8 * X ^ 2) * S := by
    linear_combination (-2 + 4 * X + 8 * X ^ 2 - (2) * S) * hG + (2) * ((2) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-16 * (X * X) + 64 * (X * X * X) + 64 * (X * X * X * X) : ℚ⟦X⟧) * G) = (-32 * X + 192 * X ^ 2 + 256 * X ^ 3) * G + (-16 * X ^ 2 + 64 * X ^ 3 + 64 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d64]
    ring
  have hR : derivative ℚ ((-8 * (X * X) + 16 * (X * X * X) + 32 * (X * X * X * X) : ℚ⟦X⟧) + (-8 * (X * X) : ℚ⟦X⟧) * S) =
      -16 * X + 48 * X ^ 2 + 128 * X ^ 3 + (-16 * X) * S + (-8 * X ^ 2) * derivative ℚ S := by
    simp [Derivation.leibniz, d8, d16, d32]
    ring
  have hk2 : (-16 * (X * X) + 64 * (X * X * X) + 64 * (X * X * X * X) : ℚ⟦X⟧) * G = (-8 * (X * X) + 16 * (X * X * X) + 32 * (X * X * X * X) : ℚ⟦X⟧) + (-8 * (X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-32 * X + 192 * X ^ 2 + 256 * X ^ 3) * G + (-16 * X ^ 2 + 64 * X ^ 3 + 64 * X ^ 4) * derivative ℚ G =
      -16 * X + 48 * X ^ 2 + 128 * X ^ 3 + (-16 * X) * S + (-8 * X ^ 2) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 4 * ((256 - 2048 * X + 3072 * X ^ 2 + 4096 * X ^ 3) * derivative ℚ G + (-512 + 6144 * X ^ 2) * G - (-512 * X + 3072 * X ^ 2)) = 0 := by
    linear_combination (-8 * X ^ 2) ^ 2 * S * hdS - 2 * (-8 * X ^ 2) ^ 2 * derivative ℚ S * hS -
      (2 * (-16 * X) * (1 - 4 * X) + (-8 * X ^ 2) * (-4)) * hk + 2 * (-8 * X ^ 2) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 4 ≠ 0 := pow_ne_zero 4 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-2 + 4 * X + 8 * X ^ 2 + (2) * S) = 4 * X ^ 2 + (0) * S) :
    derivative ℚ G * C 256 + derivative ℚ G * X * C (-2048) +
      derivative ℚ G * X * X * C 3072 + derivative ℚ G * X * X * X * C 4096 +
      G * C (-512) + G * X * X * C 6144 =
      C (-512) * X + C 3072 * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-2 + 4 * X + 8 * X ^ 2 + (2) * S) = 4 * X ^ 2 + (0) * S) (m : ℕ) :
    256 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-2048) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      3072 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 4096 * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-512) * coeff (m + 1 + 1 + 1) G + 6144 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A289684Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a289684.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  rw [e1, e2, e3]
  have r := A289684Aux.rel (S) G (by linear_combination hS)
      (by linear_combination (4 * PowerSeries.X ^ 2) * hG - ((-1) * G + (1) * S * G + (-2 * PowerSeries.X) * c * G) * hc - ((-1) * G) * hS) m
  push_cast
  linear_combination ((1 : ℚ) / 256) * r
