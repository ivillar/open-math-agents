import OMAStatements.S_oeis_a008956
import Mathlib

-- Problem: A008956, row sums of the central-factorial triangle; Mathar's product formula.
-- Upstream: formal-conjectures statements/oeis-a008956.lean (declaration OMA.S_oeis_a008956.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here. Proof: T(n,0) = 1 and T(n,k) = 0 for k > n, so the triangle recurrence gives
-- R(n+1) = ((2n+1)^2 + 1) R(n) for the row sums R(n); induction gives the product.

namespace OMA.P_oeis_a008956

open OMA.S_oeis_a008956 Finset

theorem entry_zero (n : ℕ) : entry n 0 = 1 := by
  cases n <;> rfl

theorem entry_eq_zero : ∀ n k : ℕ, n < k → entry n k = 0
  | 0, k + 1, _ => rfl
  | n + 1, k + 1, h => by
    show (2 * n + 1) ^ 2 * entry n k + entry n (k + 1) = 0
    rw [entry_eq_zero n k (by omega), entry_eq_zero n (k + 1) (by omega)]
    ring

/-- Row sums. -/
def R (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), entry n k

theorem R_succ (n : ℕ) : R (n + 1) = ((2 * n + 1) ^ 2 + 1) * R n := by
  unfold R
  rw [Finset.sum_range_succ', entry_zero]
  have h : ∀ k ∈ range (n + 1), entry (n + 1) (k + 1) = (2 * n + 1) ^ 2 * entry n k + entry n (k + 1) :=
    fun k _ => rfl
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ k ∈ range (n + 1), entry n (k + 1) + 1 = ∑ k ∈ range (n + 1), entry n k := by
    rw [Finset.sum_range_succ' (fun k => entry n k), entry_zero, Finset.sum_range_succ,
      entry_eq_zero n (n + 1) (by omega)]
  rw [add_assoc, h2]
  ring

theorem main' : ∀ n : ℕ, ∑ k ∈ range (n+1), entry n k = absOddCoefficient n := by
  intro n
  induction n with
  | zero => simp [absOddCoefficient, entry]
  | succ n ih =>
    have := R_succ n
    unfold R at this
    rw [this, ih]
    unfold absOddCoefficient
    rw [Finset.prod_range_succ]
    ring

end OMA.P_oeis_a008956

theorem OMA.solution : type_of% @OMA.S_oeis_a008956.main := OMA.P_oeis_a008956.main'
