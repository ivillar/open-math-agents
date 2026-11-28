import OMAStatements.S_oeis_a134195
import Mathlib

-- Problem: A134195, Sean A. Irvine's conjectured relation: the antidiagonal sums of A126885 are the
-- partial sums of A104879.
-- Upstream: formal-conjectures statements/oeis-a134195.lean (declaration OMA.S_oeis_a134195.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured relation holds).
-- Proof: T(q, m) = sum_{j=1..m} (1 + q + ... + q^(j-1)) by induction on m, using
-- geometric q (j+1) = q * geometric q j + 1. Then the antidiagonal sum at n+1 exceeds the one at n
-- by exactly row(n+1), and the identity follows by induction on n.

namespace OMA.P_oeis_a134195

open OMA.S_oeis_a134195 Finset

theorem gs (q j : ℕ) : geometric q (j + 1) = q * geometric q j + 1 := by
  unfold geometric
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

theorem ae (q m : ℕ) : arrayEntry q m = ∑ j ∈ range m, geometric q (j + 1) := by
  induction m with
  | zero => simp [arrayEntry]
  | succ m ih =>
    rw [arrayEntry, ih, Finset.sum_range_succ' (fun j => geometric q (j + 1))]
    have h : ∀ j ∈ range m, geometric q (j + 1 + 1) = q * geometric q (j + 1) + 1 :=
      fun j _ => gs q (j + 1)
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [geometric]
    ring

theorem step (n : ℕ) : antidiagonalSum (n + 1) = antidiagonalSum n + row (n + 1) := by
  unfold antidiagonalSum row
  simp only [ae]
  rw [Finset.sum_range_succ (fun q => ∑ j ∈ range (n + 1 + 1 - q), geometric q (j + 1)),
    Finset.sum_range_succ (fun q => geometric q (n + 1 + 1 - q))]
  have h : ∀ q ∈ range (n + 1), ∑ j ∈ range (n + 1 + 1 - q), geometric q (j + 1)
      = ∑ j ∈ range (n + 1 - q), geometric q (j + 1) + geometric q (n + 1 + 1 - q) := by
    intro q hq
    rw [Finset.mem_range] at hq
    rw [show n + 1 + 1 - q = n + 1 - q + 1 by omega, Finset.sum_range_succ]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  simp
  ring

theorem main' : ∀ n : ℕ, antidiagonalSum n = ∑ k ∈ range (n + 1), row k := by
  intro n
  induction n with
  | zero => simp [antidiagonalSum, row, arrayEntry, geometric]
  | succ n ih => rw [step, ih, Finset.sum_range_succ _ (n + 1)]

end OMA.P_oeis_a134195

theorem OMA.solution : type_of% @OMA.S_oeis_a134195.main := OMA.P_oeis_a134195.main'
