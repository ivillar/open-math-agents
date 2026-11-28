import OMAStatements.S_oeis_a306810
import Mathlib

-- Problem: A306810, the recurrence conjectured by Barker for the signed binomial transform
-- a(n) = Sum_{k=0..n} (-1)^(n+k) binomial(n,k) b(k) of the continued fraction of e (A003417).
-- Upstream: formal-conjectures statements/oeis-a306810.lean (declaration OMA.S_oeis_a306810.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated recurrence holds for n > 6).
-- Proof: b(k+6) = 2 b(k+3) - b(k) for k >= 1. With T_s(n) = Sum_k (-1)^(n+k) binomial(n,k) b(k+s),
-- T_s(n+1) = -T_s(n) + T_{s+1}(n); expanding a(n+j) = T_0(n+j) gives the combination
-- T_7 - 2 T_4 + T_1 = 0.

namespace OMA.P_oeis_a306810

open OMA.S_oeis_a306810 Finset

theorem binom_shift (f : ℕ → ℤ) (n : ℕ) :
    ∑ k ∈ range (n + 1 + 1), ((n + 1).choose k : ℤ) * f k =
      ∑ k ∈ range (n + 1), (n.choose k : ℤ) * f k +
        ∑ k ∈ range (n + 1), (n.choose k : ℤ) * f (k + 1) := by
  have h1 : ∑ k ∈ range (n + 1), (n.choose (k + 1) : ℤ) * f (k + 1) =
      ∑ k ∈ range n, (n.choose (k + 1) : ℤ) * f (k + 1) := by
    rw [sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
  have h2 : ∑ k ∈ range (n + 1), (n.choose k : ℤ) * f k =
      ∑ k ∈ range n, (n.choose (k + 1) : ℤ) * f (k + 1) + (n.choose 0 : ℤ) * f 0 :=
    sum_range_succ' _ _
  rw [sum_range_succ' _ (n + 1)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib]
  rw [h1, h2]
  simp only [Nat.choose_zero_right]
  ring

theorem b_rec (k : ℕ) (hk : 1 ≤ k) : (b (k + 6) : ℤ) = 2 * (b (k + 3) : ℤ) - (b k : ℤ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e6 : b (j + 1 + 6) = if (j + 7) % 3 = 2 then 2 * (j + 8) / 3 else 1 := rfl
  have e3 : b (j + 1 + 3) = if (j + 4) % 3 = 2 then 2 * (j + 5) / 3 else 1 := rfl
  have e0 : b (j + 1) = if (j + 1) % 3 = 2 then 2 * (j + 2) / 3 else 1 := rfl
  rw [e6, e3, e0]
  split_ifs <;> omega

noncomputable def T (s n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), (-1) ^ (n + k) * (n.choose k : ℤ) * (b (k + s) : ℤ)

theorem T_eq (s n : ℕ) :
    T s n = (-1) ^ n * ∑ k ∈ range (n + 1), (n.choose k : ℤ) * ((-1) ^ k * (b (k + s) : ℤ)) := by
  unfold T
  rw [mul_sum]
  apply sum_congr rfl
  intro k _
  ring

theorem T_shift (s n : ℕ) : T s (n + 1) = -T s n + T (s + 1) n := by
  have h := binom_shift (fun k => (-1) ^ k * (b (k + s) : ℤ)) n
  beta_reduce at h
  rw [T_eq, T_eq, T_eq, h]
  have h2 : ∑ k ∈ range (n + 1), (n.choose k : ℤ) * ((-1) ^ (k + 1) * (b (k + 1 + s) : ℤ)) =
      -∑ k ∈ range (n + 1), (n.choose k : ℤ) * ((-1) ^ k * (b (k + (s + 1)) : ℤ)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k _
    rw [show k + 1 + s = k + (s + 1) by ring]
    ring
  rw [h2]
  ring

theorem T_rec (n : ℕ) : T 7 n = 2 * T 4 n - T 1 n := by
  unfold T
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  rw [show k + 7 = (k + 1) + 6 by ring, show k + 4 = (k + 1) + 3 by ring,
    b_rec (k + 1) (by omega)]
  ring

theorem a_eq (n : ℕ) : a n = T 0 n := by
  simp only [a, T, Nat.add_zero]

theorem main' : ∀ n : ℕ, 6 < n →
    a n = -7 * a (n - 1) - 21 * a (n - 2) - 33 * a (n - 3) - 27 * a (n - 4) - 9 * a (n - 5) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
    show m + 7 - 5 = m + 2 by omega]
  simp only [a_eq, T_shift]
  linear_combination T_rec m

end OMA.P_oeis_a306810

theorem OMA.solution : type_of% @OMA.S_oeis_a306810.main := OMA.P_oeis_a306810.main'
