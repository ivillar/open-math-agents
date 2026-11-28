import OMAStatements.S_oeis_a141771

-- Problem: A141771: Expansion of (1-sqrt(1-4*x))/(2*x) + 8*x^3/((sqrt(1-4*x))*(1+sqrt(1-4*x))^3).
-- Upstream: formal-conjectures statements/oeis-a141771.lean:0 (declaration OMA.S_oeis_a141771.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its first two derivatives, divided by a common
polynomial factor, is a third order equation with polynomial coefficients and polynomial right
side rho; the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A141771Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (8 * X - 40 * X ^ 2 + 32 * X ^ 3 + (8 * X - 24 * X ^ 2) * S) = 8 * X - 32 * X ^ 2 + 16 * X ^ 4 + (8 * X - 16 * X ^ 2) * S) :
    (-65536 * X + 589824 * X ^ 2 - 1507328 * X ^ 3 + 786432 * X ^ 4) * derivative ℚ G + (-65536 + 393216 * X - 458752 * X ^ 2 - 393216 * X ^ 3) * G = -65536 + 262144 * X + 131072 * X ^ 2 - 786432 * X ^ 3 + 196608 * X ^ 4 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d384 : derivative ℚ (384 : ℚ⟦X⟧) = 0 := dnum 384
  have d512 : derivative ℚ (512 : ℚ⟦X⟧) = 0 := dnum 512
  have d640 : derivative ℚ (640 : ℚ⟦X⟧) = 0 := dnum 640
  have d1024 : derivative ℚ (1024 : ℚ⟦X⟧) = 0 := dnum 1024
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-256 * X ^ 5 + 1024 * X ^ 6) * G = (-128 * X ^ 4 + 640 * X ^ 5 - 640 * X ^ 6 + 512 * X ^ 7 : ℚ⟦X⟧) + (128 * X ^ 4 - 640 * X ^ 5 + 384 * X ^ 6) * S := by
    linear_combination (8 * X - 40 * X ^ 2 + 32 * X ^ 3 - (8 * X - 24 * X ^ 2) * S) * hG + (8 * X - 24 * X ^ 2) * ((8 * X - 24 * X ^ 2) * G - (8 * X - 16 * X ^ 2)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-256 * (X * X * X * X * X) + 1024 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-1280 * X ^ 4 + 6144 * X ^ 5) * G + (-256 * X ^ 5 + 1024 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d256, d1024]
    ring
  have hR : derivative ℚ ((-128 * (X * X * X * X) + 640 * (X * X * X * X * X) - 640 * (X * X * X * X * X * X) + 512 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (128 * (X * X * X * X) - 640 * (X * X * X * X * X) + 384 * (X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      -512 * X ^ 3 + 3200 * X ^ 4 - 3840 * X ^ 5 + 3584 * X ^ 6 + (512 * X ^ 3 - 3200 * X ^ 4 + 2304 * X ^ 5) * S + (128 * X ^ 4 - 640 * X ^ 5 + 384 * X ^ 6) * derivative ℚ S := by
    simp [Derivation.leibniz, d128, d384, d512, d640]
    ring
  have hk2 : (-256 * (X * X * X * X * X) + 1024 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (-128 * (X * X * X * X) + 640 * (X * X * X * X * X) - 640 * (X * X * X * X * X * X) + 512 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (128 * (X * X * X * X) - 640 * (X * X * X * X * X) + 384 * (X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-1280 * X ^ 4 + 6144 * X ^ 5) * G + (-256 * X ^ 5 + 1024 * X ^ 6) * derivative ℚ G =
      -512 * X ^ 3 + 3200 * X ^ 4 - 3840 * X ^ 5 + 3584 * X ^ 6 + (512 * X ^ 3 - 3200 * X ^ 4 + 2304 * X ^ 5) * S + (128 * X ^ 4 - 640 * X ^ 5 + 384 * X ^ 6) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 8 * ((1 - 4 * X) * ((-65536 * X + 589824 * X ^ 2 - 1507328 * X ^ 3 + 786432 * X ^ 4) * derivative ℚ G + (-65536 + 393216 * X - 458752 * X ^ 2 - 393216 * X ^ 3) * G - (-65536 + 262144 * X + 131072 * X ^ 2 - 786432 * X ^ 3 + 196608 * X ^ 4))) = 0 := by
    linear_combination (128 * X ^ 4 - 640 * X ^ 5 + 384 * X ^ 6) ^ 2 * S * hdS - 2 * (128 * X ^ 4 - 640 * X ^ 5 + 384 * X ^ 6) ^ 2 * derivative ℚ S * hS -
      (2 * (512 * X ^ 3 - 3200 * X ^ 4 + 2304 * X ^ 5) * (1 - 4 * X) + (128 * X ^ 4 - 640 * X ^ 5 + 384 * X ^ 6) * (-4)) * hk + 2 * (128 * X ^ 4 - 640 * X ^ 5 + 384 * X ^ 6) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 8 ≠ 0 := pow_ne_zero 8 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (8 * X - 40 * X ^ 2 + 32 * X ^ 3 + (8 * X - 24 * X ^ 2) * S) = 8 * X - 32 * X ^ 2 + 16 * X ^ 4 + (8 * X - 16 * X ^ 2) * S) :
    (-X ^ 3 + 4 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-9 * X ^ 2 + 46 * X ^ 3) * derivative ℚ (derivative ℚ G) + (28 * X ^ 2) * derivative ℚ G + (12 - 4 * X) * G =
      12 + 8 * X + 12 * X ^ 2 := by
  have h := key S G hS hG
  have d65536 : derivative ℚ (65536 : ℚ⟦X⟧) = 0 := dnum 65536
  have d131072 : derivative ℚ (131072 : ℚ⟦X⟧) = 0 := dnum 131072
  have d196608 : derivative ℚ (196608 : ℚ⟦X⟧) = 0 := dnum 196608
  have d262144 : derivative ℚ (262144 : ℚ⟦X⟧) = 0 := dnum 262144
  have d393216 : derivative ℚ (393216 : ℚ⟦X⟧) = 0 := dnum 393216
  have d458752 : derivative ℚ (458752 : ℚ⟦X⟧) = 0 := dnum 458752
  have d589824 : derivative ℚ (589824 : ℚ⟦X⟧) = 0 := dnum 589824
  have d786432 : derivative ℚ (786432 : ℚ⟦X⟧) = 0 := dnum 786432
  have d917504 : derivative ℚ (917504 : ℚ⟦X⟧) = 0 := dnum 917504
  have d1179648 : derivative ℚ (1179648 : ℚ⟦X⟧) = 0 := dnum 1179648
  have d1507328 : derivative ℚ (1507328 : ℚ⟦X⟧) = 0 := dnum 1507328
  have d2359296 : derivative ℚ (2359296 : ℚ⟦X⟧) = 0 := dnum 2359296
  have d3145728 : derivative ℚ (3145728 : ℚ⟦X⟧) = 0 := dnum 3145728
  have d4521984 : derivative ℚ (4521984 : ℚ⟦X⟧) = 0 := dnum 4521984
  have hL : derivative ℚ ((-65536 * X + 589824 * (X * X) - 1507328 * (X * X * X) + 786432 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-65536 + 393216 * X - 458752 * (X * X) - 393216 * (X * X * X) : ℚ⟦X⟧) * G) =
      (-65536 + 1179648 * X - 4521984 * X ^ 2 + 3145728 * X ^ 3) * derivative ℚ G + (-65536 * X + 589824 * X ^ 2 - 1507328 * X ^ 3 + 786432 * X ^ 4) * derivative ℚ (derivative ℚ G) + (393216 - 917504 * X - 1179648 * X ^ 2) * G + (-65536 + 393216 * X - 458752 * X ^ 2 - 393216 * X ^ 3) * derivative ℚ G := by
    simp [Derivation.leibniz, d65536, d393216, d458752, d589824, d786432, d1507328]
    ring
  have hRd : derivative ℚ (-65536 + 262144 * X + 131072 * (X * X) - 786432 * (X * X * X) + 196608 * (X * X * X * X) : ℚ⟦X⟧) = 262144 + 262144 * X - 2359296 * X ^ 2 + 786432 * X ^ 3 := by
    simp [Derivation.leibniz, d65536, d131072, d196608, d262144, d786432]
    ring
  have h2 : (-65536 * X + 589824 * (X * X) - 1507328 * (X * X * X) + 786432 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-65536 + 393216 * X - 458752 * (X * X) - 393216 * (X * X * X) : ℚ⟦X⟧) * G = (-65536 + 262144 * X + 131072 * (X * X) - 786432 * (X * X * X) + 196608 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (-65536 + 1179648 * X - 4521984 * X ^ 2 + 3145728 * X ^ 3) * derivative ℚ G + (-65536 * X + 589824 * X ^ 2 - 1507328 * X ^ 3 + 786432 * X ^ 4) * derivative ℚ (derivative ℚ G) + (393216 - 917504 * X - 1179648 * X ^ 2) * G + (-65536 + 393216 * X - 458752 * X ^ 2 - 393216 * X ^ 3) * derivative ℚ G = 262144 + 262144 * X - 2359296 * X ^ 2 + 786432 * X ^ 3 := by
    rw [← hL, h2, hRd]
  have hL2 : derivative ℚ ((-65536 + 1179648 * X - 4521984 * (X * X) + 3145728 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-65536 * X + 589824 * (X * X) - 1507328 * (X * X * X) + 786432 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (393216 - 917504 * X - 1179648 * (X * X) : ℚ⟦X⟧) * G + (-65536 + 393216 * X - 458752 * (X * X) - 393216 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (1966080 - 10878976 * X + 7077888 * X ^ 2) * derivative ℚ G + (-196608 + 2752512 * X - 9502720 * X ^ 2 + 5898240 * X ^ 3) * derivative ℚ (derivative ℚ G) + (-65536 * X + 589824 * X ^ 2 - 1507328 * X ^ 3 + 786432 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-917504 - 2359296 * X) * G := by
    simp [Derivation.leibniz, d65536, d393216, d458752, d589824, d786432, d917504, d1179648, d1507328, d3145728, d4521984]
    ring
  have hRd2 : derivative ℚ (262144 + 262144 * X - 2359296 * (X * X) + 786432 * (X * X * X) : ℚ⟦X⟧) = 262144 - 4718592 * X + 2359296 * X ^ 2 := by
    simp [Derivation.leibniz, d262144, d786432, d2359296]
    ring
  have hdp : (-65536 + 1179648 * X - 4521984 * (X * X) + 3145728 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-65536 * X + 589824 * (X * X) - 1507328 * (X * X * X) + 786432 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (393216 - 917504 * X - 1179648 * (X * X) : ℚ⟦X⟧) * G + (-65536 + 393216 * X - 458752 * (X * X) - 393216 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G = (262144 + 262144 * X - 2359296 * (X * X) + 786432 * (X * X * X) : ℚ⟦X⟧) := by linear_combination hd
  have hd2 : (1966080 - 10878976 * X + 7077888 * X ^ 2) * derivative ℚ G + (-196608 + 2752512 * X - 9502720 * X ^ 2 + 5898240 * X ^ 3) * derivative ℚ (derivative ℚ G) + (-65536 * X + 589824 * X ^ 2 - 1507328 * X ^ 3 + 786432 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-917504 - 2359296 * X) * G = 262144 - 4718592 * X + 2359296 * X ^ 2 := by
    rw [← hL2, hdp, hRd2]
  have hfull : (65536 - 655360 * X + 2031616 * X ^ 2 - 1966080 * X ^ 3 + 589824 * X ^ 4) * ((-X ^ 3 + 4 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-9 * X ^ 2 + 46 * X ^ 3) * derivative ℚ (derivative ℚ G) + (28 * X ^ 2) * derivative ℚ G + (12 - 4 * X) * G - (12 + 8 * X + 12 * X ^ 2)) = 0 := by
    linear_combination (X ^ 2 - 5 * X ^ 3 + 3 * X ^ 4) * hd2 + (6 * X - 25 * X ^ 2 + 12 * X ^ 3) * hd + (-12 + 88 * X - 48 * X ^ 2) * h
  have hg : (65536 - 655360 * X + 2031616 * X ^ 2 - 1966080 * X ^ 3 + 589824 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (65536 : ℚ⟦X⟧) = 65536 := cnum 65536
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (8 * X - 40 * X ^ 2 + 32 * X ^ 3 + (8 * X - 24 * X ^ 2) * S) = 8 * X - 32 * X ^ 2 + 16 * X ^ 4 + (8 * X - 16 * X ^ 2) * S) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C (-1) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C 4 +
      derivative ℚ (derivative ℚ G) * X * X * C (-9) + derivative ℚ (derivative ℚ G) * X * X * X * C 46 +
      derivative ℚ G * X * X * C 28 + G * C 12 +
      G * X * C (-4) =
      C 12 + C 8 * X +
      C 12 * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (8 * X - 40 * X ^ 2 + 32 * X ^ 3 + (8 * X - 24 * X ^ 2) * S) = 8 * X - 32 * X ^ 2 + 16 * X ^ 4 + (8 * X - 16 * X ^ 2) * S) (m : ℕ) :
    (-1) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G + 4 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G +
      (-9) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 46 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      28 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 12 * coeff (m + 1 + 1 + 1 + 1) G +
      (-4) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (8 * X - 40 * X ^ 2 + 32 * X ^ 3 + (8 * X - 24 * X ^ 2) * S) = 8 * X - 32 * X ^ 2 + 16 * X ^ 4 + (8 * X - 16 * X ^ 2) * S) :
    (-6) * coeff (0 + 1 + 1 + 1) G + (-54) * coeff (0 + 1 + 1 + 1) G +
      92 * coeff (0 + 1 + 1) G + 56 * coeff (0 + 1 + 1) G +
      12 * coeff (0 + 1 + 1 + 1) G + (-4) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A141771Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a141771.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  rw [e1]
  cases m with
  | zero =>
    have r := A141771Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (2 * PowerSeries.X) * hG - ((-1) * S + (-3) * S ^ 2 + (-3) * S ^ 3 + (-1) * S ^ 4) * hc - ((-8 * PowerSeries.X) + (8 * PowerSeries.X - 8 * PowerSeries.X ^ 2) * G + (1 - 4 * PowerSeries.X) * S + (6 * PowerSeries.X) * S * G + (2) * S ^ 2 + (2 * PowerSeries.X) * S ^ 2 * G + (1) * S ^ 3) * hS)
    push_cast
    linear_combination ((154 : ℚ) / 1) * r
  | succ m =>
    have r := A141771Aux.rel (S) G (by linear_combination hS)
        (by linear_combination (2 * PowerSeries.X) * hG - ((-1) * S + (-3) * S ^ 2 + (-3) * S ^ 3 + (-1) * S ^ 4) * hc - ((-8 * PowerSeries.X) + (8 * PowerSeries.X - 8 * PowerSeries.X ^ 2) * G + (1 - 4 * PowerSeries.X) * S + (6 * PowerSeries.X) * S * G + (2) * S ^ 2 + (2 * PowerSeries.X) * S ^ 2 * G + (1) * S ^ 3) * hS) m
    push_cast
    linear_combination ((1 : ℚ) / 1) * ((250 - 38 * ((m : ℚ) + 4) + 5 * ((m : ℚ) + 4) ^ 2 - ((m : ℚ) + 4) ^ 3) * r)
