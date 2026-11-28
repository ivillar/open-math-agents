import OMAStatements.S_oeis_a008749
import Mathlib

/-!
Credit: @ivillar
Proof: the denominator is (1-x)(1-x^2)(1-x^3) = 1 - x - x^2 + x^4 + x^5 - x^6, so the
coefficients c(n) of f satisfy c(n) - c(n-1) - c(n-2) + c(n-4) + c(n-5) - c(n-6) = [n = 0] +
[n = 6], which gives c(0..5) = 1, 1, 2, 3, 4, 5. The differences d(n) = c(n+1) - c(n) then
satisfy d(m+5) = d(m+3) + d(m+2) - d(m) + [m = 0], and so does b(n) (checked from its closed
form), with the same first five values 0, 1, 1, 1, 1; hence d = b by strong induction.
-/

namespace OMAA008749Helpers
open OMA.S_oeis_a008749

theorem hb6 (k : ℕ) : bSeq (k + 7) = bSeq (k + 1) + 2 := by
  show 2 * ((k + 6) / 6) + 1 + (if (k + 6 + 2) % 6 = 0 then 2 else 0) =
    2 * (k / 6) + 1 + (if (k + 2) % 6 = 0 then 2 else 0) + 2
  rw [Nat.add_div_right k (by norm_num : 0 < 6), show k + 6 + 2 = (k + 2) + 6 by ring,
    Nat.add_mod_right]
  ring

theorem b_rec (m : ℕ) : (bSeq (m + 5) : ℤ) = bSeq (m + 3) + bSeq (m + 2) - bSeq m +
    (if m = 0 then 1 else 0) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 7 with h | h
    · interval_cases m <;> decide
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 7 := ⟨m - 7, by omega⟩
      have i1 := ih (j + 1) (by omega)
      have e1 : bSeq (j + 7 + 5) = bSeq (j + 1 + 5) + 2 := hb6 (j + 5)
      have e2 : bSeq (j + 7 + 3) = bSeq (j + 1 + 3) + 2 := hb6 (j + 3)
      have e3 : bSeq (j + 7 + 2) = bSeq (j + 1 + 2) + 2 := hb6 (j + 2)
      have e4 : bSeq (j + 7) = bSeq (j + 1) + 2 := hb6 j
      rw [if_neg (by omega)] at i1 ⊢
      rw [e1, e2, e3, e4]
      push_cast
      linarith

end OMAA008749Helpers

open PowerSeries OMAA008749Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a008749.main := by
  intro f hf
  have hD : ((1 - X) * (1 - X ^ 2) * (1 - X ^ 3) : PowerSeries ℤ) =
      X ^ 0 - X ^ 1 - X ^ 2 + X ^ 4 + X ^ 5 - X ^ 6 := by
    ring
  rw [hD] at hf
  have hc : ∀ n, (if 0 ≤ n then coeff (n - 0) f else 0) - (if 1 ≤ n then coeff (n - 1) f else 0) -
      (if 2 ≤ n then coeff (n - 2) f else 0) + (if 4 ≤ n then coeff (n - 4) f else 0) +
      (if 5 ≤ n then coeff (n - 5) f else 0) - (if 6 ≤ n then coeff (n - 6) f else 0) =
      (if n = 0 then (1 : ℤ) else 0) + (if n = 6 then 1 else 0) := by
    intro n
    have h := congrArg (coeff n) hf
    rw [mul_comm] at h
    simp only [mul_add, mul_sub, map_add, map_sub, coeff_mul_X_pow', coeff_one,
      coeff_X_pow] at h
    exact h
  have c0' : constantCoeff f = 1 := by have := hc 0; norm_num at this; exact this
  have c0 : coeff 0 f = 1 := by rw [coeff_zero_eq_constantCoeff_apply]; exact c0'
  have c1 : coeff 1 f = 1 := by have := hc 1; norm_num at this; linarith
  have c2 : coeff 2 f = 2 := by have := hc 2; norm_num at this; linarith
  have c3 : coeff 3 f = 3 := by have := hc 3; norm_num at this; linarith
  have c4 : coeff 4 f = 4 := by have := hc 4; norm_num at this; linarith
  have c5 : coeff 5 f = 5 := by have := hc 5; norm_num at this; linarith
  have hr : ∀ m : ℕ, coeff (m + 6) f - coeff (m + 5) f - coeff (m + 4) f + coeff (m + 2) f +
      coeff (m + 1) f - coeff m f = if m = 0 then 1 else 0 := by
    intro m
    have h := hc (m + 6)
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_neg (by omega),
      show m + 6 - 0 = m + 6 by omega, show m + 6 - 1 = m + 5 by omega,
      show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 5 = m + 1 by omega, show m + 6 - 6 = m by omega] at h
    rw [h]
    by_cases hm : m = 0 <;> simp [hm]
  refine ⟨c0, ?_⟩
  have key : ∀ n : ℕ, coeff (n + 1) f - coeff n f = (OMA.S_oeis_a008749.bSeq n : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n 5 with h | h
      · interval_cases n
        · rw [c1, c0]; decide
        · rw [c2, c1]; decide
        · rw [c3, c2]; decide
        · rw [c4, c3]; decide
        · rw [c5, c4]; decide
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
        have i3 := ih (m + 3) (by omega)
        have i2 := ih (m + 2) (by omega)
        have i0 := ih m (by omega)
        have hb := b_rec m
        have hm := hr m
        rw [show m + 3 + 1 = m + 4 by omega] at i3
        rw [show m + 2 + 1 = m + 3 by omega] at i2
        rw [show m + 5 + 1 = m + 6 by omega]
        rw [hb]
        linarith
  intro n
  linarith [key n]
