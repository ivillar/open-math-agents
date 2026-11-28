import OMAStatements.S_oeis_a174169
import Mathlib

/-!
Credit: @ivillar
Proof: with A = sum a(n) x^n, the recursion says x^2 A^2 - (1 - x + 3x^2) A + 1 = 0. Then
S = 1 - x + 3x^2 - 2x^2 A satisfies S^2 = R with R = 1 - 2x + 3x^2 - 6x^3 + 9x^4.
Differentiating and multiplying by S gives R (2 S') = R' S, whose coefficients give a
first-order recurrence for s(k) = [x^k] S. Since s(k + 2) = -2 a(k) for k >= 1, the
conjectured recurrence at n is minus one quarter of that relation at n - 3, rewritten in a
(the term with a(n - 4) has coefficient 0 when n = 4).
-/

namespace OMAA174169Helpers
open OMA.S_oeis_a174169 PowerSeries

noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))

noncomputable def S : ℚ⟦X⟧ := 1 - X + C 3 * X ^ 2 - C 2 * (X ^ 2 * A)

theorem cA (n : ℕ) : coeff n A = (a n : ℚ) := by
  simp [A]

theorem a0 : a 0 = 1 := by rw [a]

theorem a1 : a 1 = 1 := by rw [a]

theorem a2 (n : ℕ) : a (n + 1 + 1) = a (n + 1) - 3 * a n + ∑ k : Fin (n + 1), a k * a (n - k) := by
  rw [a]

theorem conv (n : ℕ) : coeff n (A * A) = ∑ k : Fin (n + 1), (a k : ℚ) * (a (n - k) : ℚ) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ) * (a (n - k) : ℚ)) (n + 1)]
  exact Finset.sum_congr rfl (fun k _ => by simp only [cA])

theorem quad : X ^ 2 * (A * A) - A + X ^ 1 * A - C 3 * (X ^ 2 * A) + 1 = (0 : ℚ⟦X⟧) := by
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', cA, coeff_one, map_zero]
  rcases n with _ | _ | n
  · norm_num [a0]
  · norm_num [a0, a1]
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
      show n + 1 + 1 - 2 = n by omega, show n + 1 + 1 - 1 = n + 1 by omega, a2, conv]
    push_cast
    ring

theorem hS : S ^ 2 = 1 - C 2 * X + C 3 * X ^ 2 - C 6 * X ^ 3 + C 9 * X ^ 4 := by
  have q := quad
  rw [map_ofNat C 3] at q
  unfold S
  rw [map_ofNat C 3, map_ofNat C 2, map_ofNat C 6, map_ofNat C 9]
  linear_combination (4 * X ^ 2) * q

theorem h1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
  rw [derivative_pow]; norm_num

theorem h2 : d⁄dX ℚ (1 - C 2 * X + C 3 * X ^ 2 - C 6 * X ^ 3 + C 9 * X ^ 4 : ℚ⟦X⟧) =
    -(C 2) + C 6 * X - C 18 * X ^ 2 + C 36 * X ^ 3 := by
  ext k
  rw [coeff_derivative]
  rcases k with _ | _ | _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C] <;> norm_num

theorem E0 : (1 - C 2 * X + C 3 * X ^ 2 - C 6 * X ^ 3 + C 9 * X ^ 4) * (C 2 * d⁄dX ℚ S) =
    (-(C 2) + C 6 * X - C 18 * X ^ 2 + C 36 * X ^ 3) * S := by
  rw [← h2, ← hS, h1, map_ofNat C 2]
  ring

theorem T (j i1 i2 i3 i4 i5 : ℕ) (h1 : i1 = j + 1) (h2 : i2 = j + 1 + 1)
    (h3 : i3 = j + 1 + 1 + 1) (h4 : i4 = j + 1 + 1 + 1 + 1) (h5 : i5 = j + 1 + 1 + 1 + 1 + 1) :
    2 * ((j : ℚ) + 5) * coeff i5 S - 4 * ((j : ℚ) + 4) * coeff i4 S
      + 6 * ((j : ℚ) + 3) * coeff i3 S - 12 * ((j : ℚ) + 2) * coeff i2 S
      + 18 * ((j : ℚ) + 1) * coeff i1 S
      = -2 * coeff i4 S + 6 * coeff i3 S - 18 * coeff i2 S + 36 * coeff i1 S := by
  subst h1 h2 h3 h4 h5
  have h := congrArg (coeff (j + 1 + 1 + 1 + 1)) E0
  have eL : (1 - C 2 * X + C 3 * X ^ 2 - C 6 * X ^ 3 + C 9 * X ^ 4) * (C 2 * d⁄dX ℚ S) =
      C 2 * d⁄dX ℚ S - C 2 * (C 2 * (X * d⁄dX ℚ S))
        + C 3 * (C 2 * (X * (X * d⁄dX ℚ S)))
        - C 6 * (C 2 * (X * (X * (X * d⁄dX ℚ S))))
        + C 9 * (C 2 * (X * (X * (X * (X * d⁄dX ℚ S))))) := by ring
  have eR : (-(C 2) + C 6 * X - C 18 * X ^ 2 + C 36 * X ^ 3) * S =
      -(C 2 * S) + C 6 * (X * S) - C 18 * (X * (X * S)) + C 36 * (X * (X * (X * S))) := by
    ring
  rw [eL, eR] at h
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at h
  push_cast at h
  linear_combination h

theorem hs (k i : ℕ) (hk : 1 ≤ k) (hi : i = k + 2) : coeff i S = -2 * (a k : ℚ) := by
  subst hi
  unfold S
  rw [map_sub, map_add, map_sub, coeff_one, coeff_X, coeff_C_mul, coeff_X_pow, coeff_C_mul,
    coeff_X_pow_mul', if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), show k + 2 - 2 = k by omega, cA]
  ring

end OMAA174169Helpers

open OMAA174169Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a174169.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  have t := T (m + 1) (m + 2) (m + 3) (m + 4) (m + 5) (m + 6) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have g6 := hs (m + 4) (m + 6) (by omega) (by omega)
  have g5 := hs (m + 3) (m + 5) (by omega) (by omega)
  have g4 := hs (m + 2) (m + 4) (by omega) (by omega)
  have g3 := hs (m + 1) (m + 3) (by omega) (by omega)
  have g0 : (m : ℚ) * coeff (m + 2) OMAA174169Helpers.S =
      (m : ℚ) * (-2 * (OMA.S_oeis_a174169.a m : ℚ)) := by
    rcases m with _ | j
    · simp
    · rw [hs (j + 1) (j + 1 + 2) (by omega) (by omega)]
  push_cast at t
  have key : (((((m + 4 : ℕ) : ℤ) + 2) * OMA.S_oeis_a174169.a (m + 4)
      - (2 * ((m + 4 : ℕ) : ℤ) + 1) * OMA.S_oeis_a174169.a (m + 3)
      + 3 * (((m + 4 : ℕ) : ℤ) - 1) * OMA.S_oeis_a174169.a (m + 2)
      + 3 * (5 - 2 * ((m + 4 : ℕ) : ℤ)) * OMA.S_oeis_a174169.a (m + 1)
      + 9 * (((m + 4 : ℕ) : ℤ) - 4) * OMA.S_oeis_a174169.a m : ℤ) : ℚ) = 0 := by
    push_cast
    linear_combination (-1 / 4 : ℚ) * t + (((m : ℚ) + 6) / 2) * g6
      - ((2 * (m : ℚ) + 9) / 2) * g5 + (3 * ((m : ℚ) + 3) / 2) * g4
      - (3 * (2 * (m : ℚ) + 3) / 2) * g3 + (9 / 2 : ℚ) * g0
  exact_mod_cast key
