import OMAStatements.S_oeis_a203157
import Mathlib

/-!
# A203157: Mathar's recurrence

With (P, E) = products n, P(n) = T(1)⋯T(n) and E(n) = e_(n−1)(T(1), ..., T(n)), where
2T(k) = k(k+1). By induction (n+1)·E(n) = 2n·P(n) (i.e. E = P·Σ 1/T(k) = P·2n/(n+1)), and then
E(n+1) = E(n)T(n+1) + P(n) = (n+1)²·P(n). Combining the two at n = m + 1 gives
2(1 − n)E(n) + n³E(n−1) = 0.
-/

namespace PA203157
open OMA.S_oeis_a203157

theorem tri2 (k : ℕ) : 2 * tri k = (k : ℤ) * (k + 1) := by
  induction k with
  | zero => simp [tri]
  | succ k ih => rw [tri]; push_cast; linear_combination ih

theorem step (n : ℕ) :
    products (n + 1) = ((products n).1 * tri (n + 1), (products n).2 * tri (n + 1) + (products n).1) := by
  rw [products]

theorem inv (n : ℕ) : ((n : ℤ) + 1) * (products n).2 = 2 * n * (products n).1 := by
  induction n with
  | zero => simp [products]
  | succ n ih =>
    rw [step]
    have ht := tri2 (n + 1)
    push_cast at ht ⊢
    have h1 : (products n).2 * tri (n + 1) = (n : ℤ) * (n + 2) * (products n).1 := by
      have h2 : 2 * ((products n).2 * tri (n + 1)) = 2 * ((n : ℤ) * (n + 2) * (products n).1) := by
        linear_combination (products n).2 * ht + ((n : ℤ) + 2) * ih
      exact mul_left_cancel₀ (by norm_num) h2
    linear_combination ((n : ℤ) + 2) * h1 - ((n : ℤ) + 1) * (products n).1 * ht

theorem Est (n : ℕ) : (products (n + 1)).2 = ((n : ℤ) + 1) ^ 2 * (products n).1 := by
  rw [step]
  have ht := tri2 (n + 1)
  have ih := inv n
  push_cast at ht
  have h2 : 2 * ((products n).2 * tri (n + 1)) = 2 * ((n : ℤ) * (n + 2) * (products n).1) := by
    linear_combination (products n).2 * ht + ((n : ℤ) + 2) * ih
  have h1 := mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num) h2
  simp only
  linear_combination h1

end PA203157

theorem OMA.solution : type_of% @OMA.S_oeis_a203157.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  unfold OMA.S_oeis_a203157.a
  rw [PA203157.Est (m + 1)]
  have hi := PA203157.inv (m + 1)
  push_cast at hi ⊢
  linear_combination ((m : ℤ) + 2) ^ 2 * hi
