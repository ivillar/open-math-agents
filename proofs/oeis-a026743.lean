import OMAStatements.S_oeis_a026743

-- Problem: A026743: a(n) = Sum_{j=0..n} T(n,j), T given by A026736.
-- Upstream: formal-conjectures statements/oeis-a026743.lean:0 (declaration OMA.S_oeis_a026743.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A026743Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 + (0) * S) = 1 - 3 * X ^ 2 - 4 * X ^ 4 + (1 - 3 * X ^ 2) * S) :
    (4 - 44 * X ^ 2 + 156 * X ^ 4 - 164 * X ^ 6 - 48 * X ^ 8) * derivative ℚ G + (-8 - 8 * X + 56 * X ^ 2 + 16 * X ^ 3 - 88 * X ^ 4 + 88 * X ^ 5 - 24 * X ^ 6 - 96 * X ^ 7) * G = 8 * X + 16 * X ^ 2 - 48 * X ^ 3 - 96 * X ^ 4 + 24 * X ^ 5 + 48 * X ^ 6 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have hS2 : S * S = (1 - 4 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5) * G = (1 - 3 * X ^ 2 - 4 * X ^ 4 : ℚ⟦X⟧) + (1 - 3 * X ^ 2) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * (X * X) : ℚ⟦X⟧) = -8 * X := by
    simp [Derivation.leibniz, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 - 4 * X - 8 * (X * X) + 16 * (X * X * X) - 2 * (X * X * X * X) + 4 * (X * X * X * X * X) : ℚ⟦X⟧) * G) = (-4 - 16 * X + 48 * X ^ 2 - 8 * X ^ 3 + 20 * X ^ 4) * G + (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d4, d8, d16]
    ring
  have hR : derivative ℚ ((1 - 3 * (X * X) - 4 * (X * X * X * X) : ℚ⟦X⟧) + (1 - 3 * (X * X) : ℚ⟦X⟧) * S) =
      -6 * X - 16 * X ^ 3 + (-6 * X) * S + (1 - 3 * X ^ 2) * derivative ℚ S := by
    simp [Derivation.leibniz, d3, d4]
    ring
  have hk2 : (2 - 4 * X - 8 * (X * X) + 16 * (X * X * X) - 2 * (X * X * X * X) + 4 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (1 - 3 * (X * X) - 4 * (X * X * X * X) : ℚ⟦X⟧) + (1 - 3 * (X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-4 - 16 * X + 48 * X ^ 2 - 8 * X ^ 3 + 20 * X ^ 4) * G + (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5) * derivative ℚ G =
      -6 * X - 16 * X ^ 3 + (-6 * X) * S + (1 - 3 * X ^ 2) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 2 * X) * ((4 - 44 * X ^ 2 + 156 * X ^ 4 - 164 * X ^ 6 - 48 * X ^ 8) * derivative ℚ G + (-8 - 8 * X + 56 * X ^ 2 + 16 * X ^ 3 - 88 * X ^ 4 + 88 * X ^ 5 - 24 * X ^ 6 - 96 * X ^ 7) * G - (8 * X + 16 * X ^ 2 - 48 * X ^ 3 - 96 * X ^ 4 + 24 * X ^ 5 + 48 * X ^ 6)) = 0 := by
    linear_combination (1 - 3 * X ^ 2) ^ 2 * S * hdS - 2 * (1 - 3 * X ^ 2) ^ 2 * derivative ℚ S * hS -
      (2 * (-6 * X) * (1 - 4 * X ^ 2) + (1 - 3 * X ^ 2) * (-8 * X)) * hk + 2 * (1 - 3 * X ^ 2) * (1 - 4 * X ^ 2) * hdk
  have hg : (1 - 2 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 + (0) * S) = 1 - 3 * X ^ 2 - 4 * X ^ 4 + (1 - 3 * X ^ 2) * S) :
    derivative ℚ G * C 4 + derivative ℚ G * X * X * C (-44) +
      derivative ℚ G * X * X * X * X * C 156 + derivative ℚ G * X * X * X * X * X * X * C (-164) +
      derivative ℚ G * X * X * X * X * X * X * X * X * C (-48) + G * C (-8) +
      G * X * C (-8) + G * X * X * C 56 +
      G * X * X * X * C 16 + G * X * X * X * X * C (-88) +
      G * X * X * X * X * X * C 88 + G * X * X * X * X * X * X * C (-24) +
      G * X * X * X * X * X * X * X * C (-96) =
      C 8 * X + C 16 * X * X +
      C (-48) * X * X * X + C (-96) * X * X * X * X +
      C 24 * X * X * X * X * X + C 48 * X * X * X * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 + (0) * S) = 1 - 3 * X ^ 2 - 4 * X ^ 4 + (1 - 3 * X ^ 2) * S) (m : ℕ) :
    4 * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-44) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      156 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-164) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-48) * ((m : ℚ) + 1) * coeff (m + 1) G + (-8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 56 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      16 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-88) * coeff (m + 1 + 1 + 1 + 1) G +
      88 * coeff (m + 1 + 1 + 1) G + (-24) * coeff (m + 1 + 1) G +
      (-96) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 - 4 * X - 8 * X ^ 2 + 16 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 + (0) * S) = 1 - 3 * X ^ 2 - 4 * X ^ 4 + (1 - 3 * X ^ 2) * S) :
    32 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-264) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      624 * coeff (0 + 1 + 1 + 1 + 1) G + (-328) * coeff (0 + 1 + 1) G +
      (-8) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-8) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      56 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 16 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-88) * coeff (0 + 1 + 1 + 1) G + 88 * coeff (0 + 1 + 1) G +
      (-24) * coeff (0 + 1) G + (-96) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A026743Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026743.main := by
  intro R G hR _ hG n hn
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
  cases m with
  | zero =>
    have r := A026743Aux.relE0 ((1 - 2 * PowerSeries.X) * R) G (by linear_combination (1 - 2 * PowerSeries.X) * hR)
        (by linear_combination (1 - 2 * PowerSeries.X) * hG)
    push_cast
    linear_combination ((1 : ℚ) / 4) * r
  | succ m =>
    have r := A026743Aux.rel ((1 - 2 * PowerSeries.X) * R) G (by linear_combination (1 - 2 * PowerSeries.X) * hR)
        (by linear_combination (1 - 2 * PowerSeries.X) * hG) m
    push_cast
    linear_combination ((1 : ℚ) / 4) * r
