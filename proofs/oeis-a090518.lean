import OMAStatements.S_oeis_a090518
import Mathlib

/-!
# A090518: no term is zero

The set {k : 10^n / k is prime} contains 5·10^(n−1) (the quotient is 2), and 0 is not in it, so
its infimum b(n) is a nonzero element of the set; then 10^n / b(n) is prime, hence nonzero (the
witness given in the entry).
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a090518.main := by
  intro n hn
  have hne : ({k : ℕ | (10 ^ n / k).Prime} : Set ℕ).Nonempty := by
    refine ⟨5 * 10 ^ (n - 1), ?_⟩
    show (10 ^ n / (5 * 10 ^ (n - 1))).Prime
    rw [show 10 ^ n = 2 * (5 * 10 ^ (n - 1)) by
      rw [← mul_assoc, show 2 * 5 = 10 by norm_num, ← pow_succ']; congr 1; omega]
    rw [Nat.mul_div_cancel _ (by positivity)]
    exact Nat.prime_two
  have hb0 : OMA.S_oeis_a090518.b n ≠ 0 := by
    unfold OMA.S_oeis_a090518.b
    intro h0
    rcases Nat.sInf_eq_zero.mp h0 with h | h
    · simp at h; exact Nat.not_prime_zero h
    · rw [h] at hne; exact Set.not_nonempty_empty hne
  have hmem : (10 ^ n / OMA.S_oeis_a090518.b n).Prime := Nat.sInf_mem hne
  unfold OMA.S_oeis_a090518.a
  rw [if_neg hb0]
  exact hmem.ne_zero
