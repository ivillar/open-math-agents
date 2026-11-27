import OMAStatements.S_oeis_a025270

-- Problem: A025270: a(n) = a(1)*a(n-1) + a(2)*a(n-2) + ...+ a(n-1)*a(1) for n >= 5, with initial values 1,2,1,1.
-- Upstream: formal-conjectures statements/oeis-a025270.lean:0 (declaration OMA.S_oeis_a025270.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A025270Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 4 * X ^ 2 + 12 * X ^ 3 + 20 * X ^ 4)
    (hG : G * (2 + (0) * S) = 1 + (-1) * S) :
    (-4 + 16 * X + 16 * X ^ 2 - 48 * X ^ 3 - 80 * X ^ 4) * derivative ℚ G + (-8 - 16 * X + 72 * X ^ 2 + 160 * X ^ 3) * G = -4 - 8 * X + 36 * X ^ 2 + 80 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have hS2 : S * S = (1 - 4 * X - 4 * (X * X) + 12 * (X * X * X) + 20 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2) * G = (1 : ℚ⟦X⟧) + (-1) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X - 4 * (X * X) + 12 * (X * X * X) + 20 * (X * X * X * X) : ℚ⟦X⟧) = -4 - 8 * X + 36 * X ^ 2 + 80 * X ^ 3 := by
    simp [Derivation.leibniz, d4, d12, d20]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 - 8 * X + 36 * X ^ 2 + 80 * X ^ 3 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 : ℚ⟦X⟧) * G) = (0) * G + (2) * derivative ℚ G := by
    simp [Derivation.leibniz, d2]
  have hR : derivative ℚ ((1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S) =
      0 + (0) * S + (-1) * derivative ℚ S := by
    simp
  have hk2 : (2 : ℚ⟦X⟧) * G = (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (0) * G + (2) * derivative ℚ G =
      0 + (0) * S + (-1) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-1) ^ 2 * S * hdS - 2 * (-1) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 4 * X - 4 * X ^ 2 + 12 * X ^ 3 + 20 * X ^ 4) + (-1) * (-4 - 8 * X + 36 * X ^ 2 + 80 * X ^ 3)) * hk + 2 * (-1) * (1 - 4 * X - 4 * X ^ 2 + 12 * X ^ 3 + 20 * X ^ 4) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 4 * X ^ 2 + 12 * X ^ 3 + 20 * X ^ 4)
    (hG : G * (2 + (0) * S) = 1 + (-1) * S) :
    derivative ℚ G * C (-4) + derivative ℚ G * X * C 16 +
      derivative ℚ G * X * X * C 16 + derivative ℚ G * X * X * X * C (-48) +
      derivative ℚ G * X * X * X * X * C (-80) + G * C (-8) +
      G * X * C (-16) + G * X * X * C 72 +
      G * X * X * X * C 160 =
      C (-4) + C (-8) * X +
      C 36 * X * X + C 80 * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 4 * X ^ 2 + 12 * X ^ 3 + 20 * X ^ 4)
    (hG : G * (2 + (0) * S) = 1 + (-1) * S) (m : ℕ) :
    (-4) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 16 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      16 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-48) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-80) * ((m : ℚ) + 1) * coeff (m + 1) G + (-8) * coeff (m + 1 + 1 + 1 + 1) G +
      (-16) * coeff (m + 1 + 1 + 1) G + 72 * coeff (m + 1 + 1) G +
      160 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

/-- The sequence extended by 0 at index 0. -/
def gs (a : ℕ → ℚ) : ℕ → ℚ := fun n => if n = 0 then 0 else a n

set_option maxHeartbeats 4000000 in
theorem gs_zero (a : ℕ → ℚ) : gs a 0 = 0 := if_pos rfl

set_option maxHeartbeats 4000000 in
theorem gs_pos (a : ℕ → ℚ) (k : ℕ) (hk : k ≠ 0) : gs a k = a k := if_neg hk

set_option maxHeartbeats 4000000 in
theorem convR (g : ℕ → ℚ) (n : ℕ) :
    coeff n (PowerSeries.mk g * PowerSeries.mk g) = ∑ k ∈ Finset.range (n + 1), g k * g (n - k) := by
  rw [PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => g i * g j) n

set_option maxHeartbeats 4000000 in
theorem conv (g : ℕ → ℚ) (hg0 : g 0 = 0) (n : ℕ) :
    coeff n (PowerSeries.mk g * PowerSeries.mk g) = ∑ k ∈ Finset.Icc 1 (n - 1), g k * g (n - k) := by
  rw [convR]
  symm
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  · intro k hk hk'
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Icc] at hk'
    have hc : k = 0 ∨ k = n := by omega
    rcases hc with rfl | rfl
    · rw [hg0, zero_mul]
    · rw [Nat.sub_self, hg0, mul_zero]

set_option maxHeartbeats 4000000 in
theorem quadC (a : ℕ → ℚ) (h1 : a 1 = 1) (h2 : a 2 = 2) (h3 : a 3 = 1) (h4 : a 4 = 1)
    (hrec : ∀ n : ℕ, 5 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)) :
    PowerSeries.mk (gs a) * PowerSeries.mk (gs a) =
      PowerSeries.mk (gs a) - (C 1 * X ^ 1 + C 1 * X ^ 2 + C (-3) * X ^ 3 + C (-5) * X ^ 4) := by
  ext n
  rcases n with _ | _ | _ | _ | _ | m
  · rw [convR]
    simp [gs]
  · rw [convR]
    simp [Finset.sum_range_succ, gs, PowerSeries.coeff_X, h1]
  · rw [convR]
    simp [Finset.sum_range_succ, gs, PowerSeries.coeff_X, h1, h2]
    norm_num
  · rw [convR]
    simp [Finset.sum_range_succ, gs, PowerSeries.coeff_X, h1, h2, h3]
    norm_num
  · rw [convR]
    simp [Finset.sum_range_succ, gs, PowerSeries.coeff_X, h1, h2, h3, h4]
    norm_num
  · have hL := conv (gs a) (gs_zero a) (m + 1 + 1 + 1 + 1 + 1)
    have hsum : ∑ k ∈ Finset.Icc 1 (m + 1 + 1 + 1 + 1 + 1 - 1), gs a k * gs a (m + 1 + 1 + 1 + 1 + 1 - k) =
        ∑ k ∈ Finset.Icc 1 (m + 1 + 1 + 1 + 1 + 1 - 1), a k * a (m + 1 + 1 + 1 + 1 + 1 - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [gs_pos a k (by omega), gs_pos a _ (by omega)]
    have hq : coeff (m + 1 + 1 + 1 + 1 + 1) (C 1 * X ^ 1 + C 1 * X ^ 2 + C (-3) * X ^ 3 + C (-5) * X ^ 4 : ℚ⟦X⟧) = 0 := by
      simp [PowerSeries.coeff_X]
    rw [map_sub, hL, hsum, PowerSeries.coeff_mk, gs_pos a _ (by omega), hq, sub_zero]
    exact (hrec _ (by omega)).symm

set_option maxHeartbeats 4000000 in
theorem quad (a : ℕ → ℚ) (h1 : a 1 = 1) (h2 : a 2 = 2) (h3 : a 3 = 1) (h4 : a 4 = 1)
    (hrec : ∀ n : ℕ, 5 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)) :
    PowerSeries.mk (gs a) * PowerSeries.mk (gs a) = (1) * PowerSeries.mk (gs a) - (X + X ^ 2 - 3 * X ^ 3 - 5 * X ^ 4) := by
  rw [quadC a h1 h2 h3 h4 hrec]
  simp only [map_ofNat, map_neg, map_one]
  ring

end A025270Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a025270.main := by
  intro a h1 h2 h3 h4 hrec n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  rw [e1, e2, e3, e4]
  have hQ := A025270Aux.quad a h1 h2 h3 h4 hrec
  have r := A025270Aux.rel ((1 : PowerSeries ℚ) - 2 * PowerSeries.mk (A025270Aux.gs a))
      (PowerSeries.mk (A025270Aux.gs a)) (by linear_combination 4 * hQ) (by ring) m
  simp only [PowerSeries.coeff_mk, A025270Aux.gs, Nat.add_one_ne_zero, ↓reduceIte] at r
  push_cast
  linear_combination ((-1 : ℚ) / 4) * r
