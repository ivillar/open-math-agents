import OMAStatements.S_oeis_a215973
import Mathlib

/-!
Credit: @ivillar
Proof: with A = sum a(n) x^n, the recursion a(n+1) = (a(0) + ... + a(n)) + [x^n] A^2 gives
(1 - x)(A - 1) = xA + x(1 - x)A^2. Then S = (1 - 2x) - 2x(1 - x)A satisfies S^2 = R with
R = 1 - 8x + 12x^2 - 4x^3. Differentiating and multiplying by S gives R (2 S') = R' S, whose
coefficients give a first-order recurrence for s(k) = [x^k] S. Since
s(k + 2) = -2 a(k + 1) + 2 a(k), the conjectured recurrence at n is minus one quarter of that
relation at n, rewritten in a.
-/

namespace OMAA215973Helpers
open OMA.S_oeis_a215973 PowerSeries

noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))

noncomputable def S : ℚ⟦X⟧ := 1 - C 2 * X - C 2 * (X ^ 1 * A) + C 2 * (X ^ 2 * A)

theorem cA (n : ℕ) : coeff n A = (a n : ℚ) := by
  simp [A]

theorem a0 : a 0 = 1 := by rw [a]

theorem a1 (n : ℕ) : a (n + 1) = ∑ k : Fin (n + 1), a k * (1 + a (n - k)) := by
  rw [a]

theorem ha1 : a 1 = 2 := by
  rw [a1]
  simp [a0]

theorem ccA : constantCoeff A = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, cA, a0]
  norm_num

theorem conv (n : ℕ) :
    coeff n (A * A) = ∑ k ∈ Finset.range (n + 1), (a k : ℚ) * (a (n - k) : ℚ) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact Finset.sum_congr rfl (fun k _ => by simp only [cA])

theorem rec' (n : ℕ) :
    (a (n + 1) : ℚ) = ∑ k ∈ Finset.range (n + 1), (a k : ℚ) + coeff n (A * A) := by
  rw [a1, conv]
  push_cast
  rw [Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ) * (1 + (a (n - k) : ℚ))) (n + 1)]
  simp only [mul_add, mul_one, Finset.sum_add_distrib]

theorem quad : A - 1 - C 2 * (X ^ 1 * A) + X - X ^ 1 * (A * A) + X ^ 2 * (A * A) =
    (0 : ℚ⟦X⟧) := by
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', cA, coeff_one, coeff_X, map_zero]
  rcases n with _ | _ | q
  · norm_num [a0]
  · norm_num [a0, ha1, ccA]
  · have r1 := rec' (q + 1)
    have r0 := rec' q
    have hP : ∑ k ∈ Finset.range (q + 1 + 1), (a k : ℚ) =
        ∑ k ∈ Finset.range (q + 1), (a k : ℚ) + (a (q + 1) : ℚ) := Finset.sum_range_succ _ _
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
      if_pos (by omega), show q + 1 + 1 - 1 = q + 1 by omega, show q + 1 + 1 - 2 = q by omega]
    linear_combination r1 - r0 + hP

theorem hS : S ^ 2 = 1 - C 8 * X + C 12 * X ^ 2 - C 4 * X ^ 3 := by
  have q := quad
  rw [map_ofNat C 2] at q
  unfold S
  rw [map_ofNat C 2, map_ofNat C 8, map_ofNat C 12, map_ofNat C 4]
  linear_combination (-4 * X * (1 - X)) * q

theorem h1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
  rw [derivative_pow]; norm_num

theorem h2 : d⁄dX ℚ (1 - C 8 * X + C 12 * X ^ 2 - C 4 * X ^ 3 : ℚ⟦X⟧) =
    -(C 8) + C 24 * X - C 12 * X ^ 2 := by
  ext k
  rw [coeff_derivative]
  rcases k with _ | _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C] <;> norm_num

theorem E0 : (1 - C 8 * X + C 12 * X ^ 2 - C 4 * X ^ 3) * (C 2 * d⁄dX ℚ S) =
    (-(C 8) + C 24 * X - C 12 * X ^ 2) * S := by
  rw [← h2, ← hS, h1, map_ofNat C 2]
  ring

theorem T (j i1 i2 i3 i4 : ℕ) (h1 : i1 = j + 1) (h2 : i2 = j + 1 + 1)
    (h3 : i3 = j + 1 + 1 + 1) (h4 : i4 = j + 1 + 1 + 1 + 1) :
    2 * ((j : ℚ) + 4) * coeff i4 S - 16 * ((j : ℚ) + 3) * coeff i3 S
      + 24 * ((j : ℚ) + 2) * coeff i2 S - 8 * ((j : ℚ) + 1) * coeff i1 S
      = -8 * coeff i3 S + 24 * coeff i2 S - 12 * coeff i1 S := by
  subst h1 h2 h3 h4
  have h := congrArg (coeff (j + 1 + 1 + 1)) E0
  have eL : (1 - C 8 * X + C 12 * X ^ 2 - C 4 * X ^ 3) * (C 2 * d⁄dX ℚ S) =
      C 2 * d⁄dX ℚ S - C 8 * (C 2 * (X * d⁄dX ℚ S))
        + C 12 * (C 2 * (X * (X * d⁄dX ℚ S)))
        - C 4 * (C 2 * (X * (X * (X * d⁄dX ℚ S)))) := by ring
  have eR : (-(C 8) + C 24 * X - C 12 * X ^ 2) * S =
      -(C 8 * S) + C 24 * (X * S) - C 12 * (X * (X * S)) := by ring
  rw [eL, eR] at h
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at h
  push_cast at h
  linear_combination h

theorem hs (k i i1 : ℕ) (hi : i = k + 2) (hi1 : i1 = k + 1) :
    coeff i S = -2 * (a i1 : ℚ) + 2 * (a k : ℚ) := by
  subst hi hi1
  unfold S
  rw [map_add, map_sub, map_sub, coeff_one, coeff_C_mul, coeff_X, coeff_C_mul,
    coeff_X_pow_mul', coeff_C_mul, coeff_X_pow_mul', if_neg (by omega), if_neg (by omega),
    if_pos (by omega), if_pos (by omega), show k + 2 - 1 = k + 1 by omega,
    show k + 2 - 2 = k by omega, cA, cA]
  ring

end OMAA215973Helpers

open OMAA215973Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a215973.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  have t := T (m + 1) (m + 2) (m + 3) (m + 4) (m + 5) (by omega) (by omega) (by omega)
    (by omega)
  have g5 := hs (m + 3) (m + 5) (m + 4) (by omega) (by omega)
  have g4 := hs (m + 2) (m + 4) (m + 3) (by omega) (by omega)
  have g3 := hs (m + 1) (m + 3) (m + 2) (by omega) (by omega)
  have g2 := hs m (m + 2) (m + 1) (by omega) (by omega)
  push_cast at t
  have key : (((((m + 4 : ℕ) : ℤ) + 1) * OMA.S_oeis_a215973.a (m + 4)
      + 3 * (-3 * ((m + 4 : ℕ) : ℤ) + 1) * OMA.S_oeis_a215973.a (m + 3)
      + 4 * (5 * ((m + 4 : ℕ) : ℤ) - 7) * OMA.S_oeis_a215973.a (m + 2)
      + 2 * (-8 * ((m + 4 : ℕ) : ℤ) + 19) * OMA.S_oeis_a215973.a (m + 1)
      + 2 * (2 * ((m + 4 : ℕ) : ℤ) - 7) * OMA.S_oeis_a215973.a m : ℤ) : ℚ) = 0 := by
    push_cast
    linear_combination (-1 / 4 : ℚ) * t + (((m : ℚ) + 5) / 2) * g5
      - (4 * (m : ℚ) + 14) * g4 + (6 * (m : ℚ) + 12) * g3 - (2 * (m : ℚ) + 1) * g2
  exact_mod_cast key
