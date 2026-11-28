import OMAStatements.S_oeis_a166587
import Mathlib

/-!
Credit: @ivillar
Proof (following the remark of Robert Israel in the entry): differentiating S^2 = P with
P = 1 + 2x - 3x^2 and multiplying by S gives P * (2 S') = (2 - 6x) S. Reading off the
coefficient of x^(j+2) gives, with s(k) = [x^k] S,
2(j+3) s(j+3) + 4(j+2) s(j+2) - 6(j+1) s(j+1) = 2 s(j+2) - 6 s(j+1).
From 2xG = 1 + 3x - S, a(k) = -s(k+1)/2 for k >= 1. Mathar's recurrence at n is then
n times the first-order relation at n minus (n-2) times the relation at n-1 (the term
with a(n-3) has coefficient 0 when n = 3).
-/

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a166587.main := by
  intro S G hS _ hG n hn
  have hS' : S ^ 2 = 1 + C 2 * X - C 3 * X ^ 2 := by rw [hS, map_ofNat C 2, map_ofNat C 3]
  have h1 : d⁄dX ℚ (S ^ 2) = 2 * S * d⁄dX ℚ S := by
    rw [derivative_pow]; norm_num
  have h2 : d⁄dX ℚ (1 + C 2 * X - C 3 * X ^ 2 : ℚ⟦X⟧) = C 2 - C 6 * X := by
    ext k
    rw [coeff_derivative]
    rcases k with _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C]
    norm_num
  have E0 : (1 + C 2 * X - C 3 * X ^ 2) * (C 2 * d⁄dX ℚ S) = (C 2 - C 6 * X) * S := by
    rw [← h2, ← hS', h1, map_ofNat C 2]
    ring
  have T : ∀ j a b c : ℕ, a = j + 1 → b = j + 1 + 1 → c = j + 1 + 1 + 1 →
      2 * ((j : ℚ) + 3) * coeff c S + 4 * ((j : ℚ) + 2) * coeff b S
        - 6 * ((j : ℚ) + 1) * coeff a S = 2 * coeff b S - 6 * coeff a S := by
    intro j a b c ha hb hc
    subst ha hb hc
    have h := congrArg (coeff (j + 1 + 1)) E0
    have eL : (1 + C 2 * X - C 3 * X ^ 2) * (C 2 * d⁄dX ℚ S) =
        C 2 * d⁄dX ℚ S + C 2 * (C 2 * (X * d⁄dX ℚ S))
          - C 3 * (C 2 * (X * (X * d⁄dX ℚ S))) := by ring
    have eR : (C 2 - C 6 * X) * S = C 2 * S - C 6 * (X * S) := by ring
    rw [eL, eR] at h
    simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at h
    push_cast at h
    linear_combination h
  have hG' : C 2 * (X * G) = 1 + C 3 * X - S := by
    rw [map_ofNat C 2, map_ofNat C 3, ← hG]; ring
  have hg : ∀ a b : ℕ, 1 ≤ a → b = a + 1 → 2 * coeff a G = - coeff b S := by
    intro a b ha hb
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
    subst hb
    have h := congrArg (coeff (k + 1 + 1)) hG'
    simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_one, coeff_X,
      show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, if_false] at h
    linear_combination h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  push_cast
  have g3 := hg (m + 3) (m + 4) (by omega) (by omega)
  have g2 := hg (m + 2) (m + 3) (by omega) (by omega)
  have g1 := hg (m + 1) (m + 2) (by omega) (by omega)
  have g0 : 3 * ((m : ℚ) + 1) * m * coeff m G =
      3 * ((m : ℚ) + 1) * m * (-(coeff (m + 1) S) / 2) := by
    rcases m with _ | j
    · simp
    · have h := hg (j + 1) (j + 1 + 1) (by omega) (by omega)
      linear_combination (3 * (((j + 1 : ℕ) : ℚ) + 1) * ((j + 1 : ℕ) : ℚ) / 2) * h
  have E1 := T (m + 1) (m + 2) (m + 3) (m + 4) (by omega) (by omega) (by omega)
  have E2 := T m (m + 1) (m + 2) (m + 3) (by omega) (by omega) (by omega)
  push_cast at E1 E2
  linear_combination (((m : ℚ) + 3) * ((m : ℚ) + 4) / 2) * g3
    + (((m : ℚ) + 3) * ((m : ℚ) + 4) / 2) * g2
    - ((5 * ((m : ℚ) + 3) - 3) * ((m : ℚ) + 1) / 2) * g1 + g0
    - (((m : ℚ) + 3) / 4) * E1 + (((m : ℚ) + 1) / 4) * E2
