import OMAStatements.S_oeis_a039692
import Mathlib

-- Problem: A039692, row sums of the Jabotinsky triangle equal n! F(n+1).
-- Upstream: formal-conjectures statements/oeis-a039692.lean (declaration OMA.S_oeis_a039692.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here. Proof: exchange the sums; the Stirling row sum is sum_m s(k,m) = k!, which
-- cancels the k! in the denominator, and sum_k C(k, n-k) = F(n+1) (Mathlib fib_succ_eq_sum_choose).

namespace OMA.P_oeis_a039692

open OMA.S_oeis_a039692 Finset

theorem stirling_row_sum : ∀ k : ℕ,
    ∑ m ∈ range (k + 1), Nat.stirlingFirst k m = k.factorial
  | 0 => by simp
  | k + 1 => by
    rw [Finset.sum_range_succ', Nat.stirlingFirst_succ_zero, add_zero]
    simp only [Nat.stirlingFirst_succ_succ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ i ∈ range (k + 1), Nat.stirlingFirst k (i + 1) = k.factorial - Nat.stirlingFirst k 0 := by
      have := stirling_row_sum k
      rw [Finset.sum_range_succ'] at this
      have h2 : ∑ i ∈ range (k + 1), Nat.stirlingFirst k (i + 1) =
          ∑ i ∈ range k, Nat.stirlingFirst k (i + 1) := by
        rw [Finset.sum_range_succ, Nat.stirlingFirst_eq_zero_of_lt (by omega), add_zero]
      rw [h2]
      omega
    rw [h1, stirling_row_sum k, Nat.factorial_succ]
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · rw [show Nat.stirlingFirst k 0 = 0 by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact Nat.stirlingFirst_succ_zero j]
      rw [Nat.sub_zero]
      ring

theorem stirling_sum_le (k n : ℕ) (hk : k ≤ n) :
    ∑ m ∈ range (n + 1), (Nat.stirlingFirst k m : ℚ) = (k.factorial : ℚ) := by
  rw [← stirling_row_sum k]
  push_cast
  rw [← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ n + 1 by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico (k + 1) (n + 1)), add_zero]
  intro m hm
  rw [Finset.mem_Ico] at hm
  rw [Nat.stirlingFirst_eq_zero_of_lt (by omega)]
  simp

theorem main' : ∀ n : ℕ, 0<n → ∑ m ∈ range (n+1), entry n m =
    (n.factorial:ℚ)*(Nat.fib (n+1):ℚ) := by
  intro n hn
  unfold entry
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  have h : ∀ k ∈ range (n + 1), ∑ m ∈ range (n + 1),
      (Nat.stirlingFirst k m : ℚ) * (k.choose (n - k) : ℚ) / k.factorial = (k.choose (n - k) : ℚ) := by
    intro k hk
    have hk' : k ≤ n := by simp at hk; omega
    rw [show (∑ m ∈ range (n + 1), (Nat.stirlingFirst k m : ℚ) * (k.choose (n - k) : ℚ) / k.factorial)
        = (∑ m ∈ range (n + 1), (Nat.stirlingFirst k m : ℚ)) * (k.choose (n - k) : ℚ) / k.factorial by
      rw [Finset.sum_mul, Finset.sum_div]]
    rw [stirling_sum_le k n hk']
    have : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  rw [Finset.sum_congr rfl h, Nat.fib_succ_eq_sum_choose,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => i.choose j)]
  push_cast
  rfl

end OMA.P_oeis_a039692

theorem OMA.solution : type_of% @OMA.S_oeis_a039692.main := OMA.P_oeis_a039692.main'
