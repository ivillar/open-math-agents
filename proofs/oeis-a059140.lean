import OMAStatements.S_oeis_a059140
import Mathlib

/-!
Credit: @ivillar
Proof: the k-th collapsed phrase is 3 v(k) + 4, where v is the 2-adic valuation. Splitting
1..2^(m+1)-1 into odd and even numbers shows that V(m) = sum of v(k) over 1 <= k < 2^m satisfies
V(m+1) = V(m) + 2^m - 1, so V(m) = 2^m - m - 1 (Legendre). Hence
a(n) = 3 V(n+1) + 4 (2^(n+1) - 1) = 2 (-5 + 7 * 2^n) - 3n. The recurrence and the generating
function follow from this closed form by direct computation.
-/

namespace OMAA059140Helpers
open OMA.S_oeis_a059140 PowerSeries

theorem split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ k ∈ Finset.range (2 * N + 1), f (k + 1) =
      ∑ j ∈ Finset.range (N + 1), f (2 * j + 1) + ∑ j ∈ Finset.range N, f (2 * j + 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have l1 : ∑ k ∈ Finset.range (2 * (N + 1) + 1), f (k + 1) =
        ∑ k ∈ Finset.range (2 * N + 1), f (k + 1) + f (2 * N + 2) + f (2 * N + 3) := by
      rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ]
    have l2 : ∑ j ∈ Finset.range (N + 1 + 1), f (2 * j + 1) =
        ∑ j ∈ Finset.range (N + 1), f (2 * j + 1) + f (2 * N + 3) := Finset.sum_range_succ _ _
    have l3 : ∑ j ∈ Finset.range (N + 1), f (2 * j + 2) =
        ∑ j ∈ Finset.range N, f (2 * j + 2) + f (2 * N + 2) := Finset.sum_range_succ _ _
    rw [l1, l2, l3, ih]
    abel

theorem V (m : ℕ) :
    ∑ k ∈ Finset.range (2 ^ m - 1), (padicValNat 2 (k + 1) : ℤ) = 2 ^ m - m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by
      have := Nat.one_le_two_pow (n := m)
      rw [pow_succ]
      omega
    have e1 : ∀ j : ℕ, padicValNat 2 (2 * j + 1) = 0 := fun j =>
      padicValNat.eq_zero_of_not_dvd (by omega)
    have e2 : ∀ j : ℕ, padicValNat 2 (2 * j + 2) = padicValNat 2 (j + 1) + 1 := by
      intro j
      rw [show 2 * j + 2 = 2 * (j + 1) by ring, padicValNat.mul (by norm_num) (by omega),
        padicValNat_self]
      ring
    rw [h2, split (fun k => (padicValNat 2 k : ℤ))]
    simp only [e1, e2, Nat.cast_zero, Nat.cast_add, Nat.cast_one, Finset.sum_const_zero, zero_add,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, ih]
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring

theorem closed (n : ℕ) : (a n : ℤ) = 2 * (-5 + 7 * 2 ^ n) - 3 * n := by
  have hc : ∀ k, collapsed k = 3 * padicValNat 2 k + 4 := by
    intro k
    simp only [collapsed, phrase, ruler, List.sum_cons, List.sum_nil]
    ring
  unfold a
  rw [Nat.cast_sum]
  simp only [hc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, V, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  ring

theorem coeff_mk_mul_X_pow (f : ℕ → ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (f : ℕ → ℚ) (r : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * (if k ≤ n then f (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

end OMAA059140Helpers

open OMAA059140Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a059140.main := by
  have hq : ∀ n, (OMA.S_oeis_a059140.a n : ℚ) = 2 * (-5 + 7 * 2 ^ n) - 3 * n := by
    intro n
    exact_mod_cast closed n
  refine ⟨closed, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega, closed (m + 3), closed (m + 2), closed (m + 1), closed m]
    push_cast
    ring
  · ext n
    have hD : ((X - 1) ^ 2 * (2 * X - 1) : PowerSeries ℚ) =
        C 2 * X ^ 3 - C 5 * X ^ 2 + C 4 * X ^ 1 - X ^ 0 := by
      rw [map_ofNat C 2, map_ofNat C 5, map_ofNat C 4]; ring
    have hN : (X - 4 : PowerSeries ℚ) = X ^ 1 - C 4 * X ^ 0 := by
      rw [map_ofNat C 4]; ring
    rw [hD, hN]
    simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
      coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num [hq]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
        if_neg (by omega), if_neg (by omega), show m + 3 - 3 = m by omega, show m + 3 - 2 = m + 1 by omega,
        show m + 3 - 1 = m + 2 by omega, show m + 3 - 0 = m + 3 by omega, hq, hq, hq, hq]
      push_cast
      ring
