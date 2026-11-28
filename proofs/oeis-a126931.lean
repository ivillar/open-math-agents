import OMAStatements.S_oeis_a126931
import Mathlib

/-!
Credit: @ivillar
Proof: with A = sum a(n) x^n, the recursion says A = 1 + 6xA - 3xA^2 + 10x^2 A^2. Then
S = (1 - 6x) + 2(3x - 10x^2) A satisfies S^2 = 1 - 4x^2. Differentiating and multiplying by S
gives (1 - 4x^2) (2 S') = -8x S, so (k + 1) s(k + 1) = 4 (k - 2) s(k - 1) for s(k) = [x^k] S.
Since s(k + 2) = 6 a(k + 1) - 20 a(k), the conjectured recurrence at n is one quarter of
that relation at k = n, rewritten in terms of a.
-/

namespace OMAA126931Helpers
open OMA.S_oeis_a126931 PowerSeries

noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))

noncomputable def S : ℚ⟦X⟧ := 1 - C 6 * X + C 6 * (X ^ 1 * A) - C 20 * (X ^ 2 * A)

theorem cA (n : ℕ) : coeff n A = (a n : ℚ) := by
  simp [A]

theorem a0 : a 0 = 1 := by rw [a]

theorem a1 : a 1 = 3 := by rw [a]

theorem a2 (n : ℕ) : a (n + 1 + 1) = 6 * a (n + 1)
    - 3 * ∑ k : Fin (n + 1 + 1), a k * a (n + 1 - k)
    + 10 * ∑ k : Fin (n + 1), a k * a (n - k) := by
  rw [a]

theorem conv (n : ℕ) : coeff n (A * A) = ∑ k : Fin (n + 1), (a k : ℚ) * (a (n - k) : ℚ) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ) * (a (n - k) : ℚ)) (n + 1)]
  exact Finset.sum_congr rfl (fun k _ => by simp only [cA])

theorem quad : C 10 * (X ^ 2 * (A * A)) - C 3 * (X ^ 1 * (A * A)) + C 6 * (X ^ 1 * A) - A + 1 =
    (0 : ℚ⟦X⟧) := by
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', cA, coeff_one, map_zero]
  rcases n with _ | _ | n
  · norm_num [a0]
  · simp only [conv]
    norm_num [a0, a1]
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
      show n + 1 + 1 - 2 = n by omega, show n + 1 + 1 - 1 = n + 1 by omega, a2, conv, conv]
    push_cast
    ring

theorem hS : S ^ 2 = 1 - C 4 * X ^ 2 := by
  have q := quad
  rw [map_ofNat C 10, map_ofNat C 3, map_ofNat C 6] at q
  unfold S
  rw [map_ofNat C 6, map_ofNat C 20, map_ofNat C 4]
  linear_combination (-4 * (3 * X - 10 * X ^ 2)) * q

theorem h1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
  rw [derivative_pow]; norm_num

theorem h2 : d⁄dX ℚ (1 - C 4 * X ^ 2 : ℚ⟦X⟧) = -(C 8 * X) := by
  ext k
  rw [coeff_derivative]
  rcases k with _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C]
  norm_num

theorem E0 : (1 - C 4 * X ^ 2) * (C 2 * d⁄dX ℚ S) = (-(C 8 * X)) * S := by
  rw [← h2, ← hS, h1, map_ofNat C 2]
  ring

theorem T (j i1 i3 : ℕ) (h1 : i1 = j + 1) (h3 : i3 = j + 1 + 1 + 1) :
    2 * ((j : ℚ) + 3) * coeff i3 S - 8 * ((j : ℚ) + 1) * coeff i1 S = -8 * coeff i1 S := by
  subst h1 h3
  have h := congrArg (coeff (j + 1 + 1)) E0
  have eL : (1 - C 4 * X ^ 2) * (C 2 * d⁄dX ℚ S) =
      C 2 * d⁄dX ℚ S - C 4 * (C 2 * (X * (X * d⁄dX ℚ S))) := by ring
  have eR : (-(C 8 * X)) * S = -(C 8 * (X * S)) := by ring
  rw [eL, eR] at h
  simp only [map_sub, map_neg, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at h
  push_cast at h
  linear_combination h

theorem hs (k i i' : ℕ) (hi : i = k + 2) (hi' : i' = k + 1) :
    coeff i S = 6 * (a i' : ℚ) - 20 * (a k : ℚ) := by
  subst hi hi'
  simp [S, coeff_X_pow_mul', cA, coeff_one]

end OMAA126931Helpers

open OMAA126931Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a126931.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  have t := T (m + 1) (m + 2) (m + 4) (by omega) (by omega)
  have g3 := hs (m + 2) (m + 4) (m + 3) (by omega) (by omega)
  have g1 := hs m (m + 2) (m + 1) (by omega) (by omega)
  push_cast at t
  have key : ((3 * (((m + 3 : ℕ) : ℤ) + 1) * OMA.S_oeis_a126931.a (m + 3)
      + 10 * (-((m + 3 : ℕ) : ℤ) - 1) * OMA.S_oeis_a126931.a (m + 2)
      + 12 * (-((m + 3 : ℕ) : ℤ) + 2) * OMA.S_oeis_a126931.a (m + 1)
      + 40 * (((m + 3 : ℕ) : ℤ) - 2) * OMA.S_oeis_a126931.a m : ℤ) : ℚ) = 0 := by
    push_cast
    linear_combination (1 / 4 : ℚ) * t - (((m : ℚ) + 4) / 2) * g3 + (2 * ((m : ℚ) + 1)) * g1
  exact_mod_cast key
