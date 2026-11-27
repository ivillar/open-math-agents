import OMAStatements.S_oeis_a155151
import Mathlib

/-!
# A155151: 2^p in the triangle forces 2^p − 1 composite

T(n,k) − 1 = (2n+1)(2k+1), so T(n,k) = 2^p gives 2^p − 1 = (2n+1)(2k+1) with both factors at
least 3 when 1 ≤ k ≤ n; hence 2^p − 1 is not prime (the argument in the entry).
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a155151.main := by
  rintro p hp ⟨n, k, hk, hkn, hT⟩
  unfold OMA.S_oeis_a155151.T at hT
  have h : 2 ^ p - 1 = (2 * n + 1) * (2 * k + 1) := by
    have : (2 * n + 1) * (2 * k + 1) + 1 = 2 ^ p := by rw [← hT]; ring
    omega
  rw [h, Nat.prime_mul_iff]
  omega
