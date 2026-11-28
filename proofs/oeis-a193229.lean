import OMAStatements.S_oeis_a193229
import Mathlib

/-!
Credit: @ivillar
Proof: from the recursion, T(n+1, n+1) = (n+1) T(n, n), T(n+1, 0) = T(n+1, 1) and, for
1 <= k <= n+1, T(n+1, k) = T(n+1, k+1) + k T(n, k-1) (the two sums differ only in the term
i = k - 1). With r = n - k, the claim reads 2^r r! T(n, n-r) = (n+r)!, which follows by
induction on n and, inside row n+1, on r: 2^(r+1) (r+1)! T(n+1, n-r) =
2(r+1) (n+r+1)! + (n-r) (n+r+1)! = (n+r+2)!, and similarly for the edge cases.
-/

namespace OMAA193229Helpers
open OMA.S_oeis_a193229

theorem T_top (n : ℕ) : a193229 (n + 1) (n + 1) = (n + 1) * a193229 n n := by
  show (∑ i ∈ Finset.range (n + 1), if n + 1 ≤ i + 1 then (i + 1) * a193229 n i else 0) = _
  rw [Finset.sum_range_succ, if_pos le_rfl, Finset.sum_eq_zero, zero_add]
  intro i hi
  rw [Finset.mem_range] at hi
  rw [if_neg (by omega)]

theorem T_zero (n : ℕ) : a193229 (n + 1) 0 = a193229 (n + 1) 1 := by
  show (∑ i ∈ Finset.range (n + 1), if 0 ≤ i + 1 then (i + 1) * a193229 n i else 0) =
    (∑ i ∈ Finset.range (n + 1), if 1 ≤ i + 1 then (i + 1) * a193229 n i else 0)
  apply Finset.sum_congr rfl
  intro i _
  rw [if_pos (by omega), if_pos (by omega)]

theorem T_step (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n + 1) :
    a193229 (n + 1) k = a193229 (n + 1) (k + 1) + k * a193229 n (k - 1) := by
  show (∑ i ∈ Finset.range (n + 1), if k ≤ i + 1 then (i + 1) * a193229 n i else 0) =
    (∑ i ∈ Finset.range (n + 1), if k + 1 ≤ i + 1 then (i + 1) * a193229 n i else 0) +
      k * a193229 n (k - 1)
  have h : ∀ i ∈ Finset.range (n + 1), (if k ≤ i + 1 then (i + 1) * a193229 n i else 0) =
      (if k + 1 ≤ i + 1 then (i + 1) * a193229 n i else 0) +
        (if k - 1 = i then k * a193229 n i else 0) := by
    intro i _
    by_cases h1 : k + 1 ≤ i + 1
    · rw [if_pos (by omega), if_pos h1, if_neg (by omega), add_zero]
    · by_cases h2 : k ≤ i + 1
      · have hik : i + 1 = k := by omega
        rw [if_pos h2, if_neg h1, if_pos (by omega), zero_add, hik]
      · rw [if_neg h2, if_neg h1, if_neg (by omega), add_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.mpr (by omega))]

theorem Q (n : ℕ) : ∀ r, r ≤ n → 2 ^ r * r.factorial * a193229 n (n - r) = (n + r).factorial := by
  induction n with
  | zero =>
    intro r hr
    obtain rfl : r = 0 := by omega
    rfl
  | succ n ih =>
    intro r
    induction r with
    | zero =>
      intro _
      have h0 := ih 0 (by omega)
      simp only [pow_zero, Nat.factorial_zero, one_mul, Nat.sub_zero, add_zero] at h0 ⊢
      rw [T_top, h0, Nat.factorial_succ]
    | succ r ihr =>
      intro hr
      have hprev := ihr (by omega)
      rw [show n + 1 - r = (n - r) + 1 by omega] at hprev
      rcases Nat.lt_or_ge r n with hrn | hrn
      · have hrow := ih (r + 1) (by omega)
        rw [show n - (r + 1) = n - r - 1 by omega] at hrow
        rw [show n + 1 - (r + 1) = n - r by omega,
          T_step n (n - r) (by omega) (by omega), show n - r - 1 = n - (r + 1) + 0 by omega,
          show n - (r + 1) + 0 = n - r - 1 by omega]
        rw [pow_succ, Nat.factorial_succ]
        have e1 : 2 ^ r * 2 * ((r + 1) * r.factorial) *
            (a193229 (n + 1) (n - r + 1) + (n - r) * a193229 n (n - r - 1)) =
            2 * (r + 1) * (2 ^ r * r.factorial * a193229 (n + 1) (n - r + 1)) +
            (n - r) * (2 ^ (r + 1) * (r + 1).factorial * a193229 n (n - r - 1)) := by
          rw [Nat.factorial_succ, pow_succ]
          ring
        rw [e1, hprev, hrow, show n + 1 + (r + 1) = (n + r + 1) + 1 by ring,
          Nat.factorial_succ (n + r + 1), show n + 1 + r = n + r + 1 by ring,
          show n + (r + 1) = n + r + 1 by ring]
        have : n - r + 2 * (r + 1) = n + r + 1 + 1 := by omega
        nlinarith [this]
      · obtain rfl : n = r := by omega
        rw [show n + 1 - (n + 1) = 0 by omega, T_zero, pow_succ, Nat.factorial_succ]
        have e2 : 2 ^ n * 2 * ((n + 1) * n.factorial) * a193229 (n + 1) 1 =
            2 * (n + 1) * (2 ^ n * n.factorial * a193229 (n + 1) (n - n + 1)) := by
          rw [show n - n + 1 = 1 by omega]
          ring
        rw [e2, hprev, show n + 1 + (n + 1) = (n + 1 + n) + 1 by ring,
          Nat.factorial_succ (n + 1 + n)]
        ring

end OMAA193229Helpers

open OMAA193229Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a193229.main := by
  intro n k hk
  have h := Q n (n - k) (by omega)
  rw [show n - (n - k) = k by omega, show n + (n - k) = 2 * n - k by omega] at h
  exact h
