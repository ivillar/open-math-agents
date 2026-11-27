import OMAStatements.S_oeis_a090525
import Mathlib

/-!
# A090525: no term is zero

The infimum is 0 only if 0 is in the set (n^n / 0 = 0 is not prime) or the set is empty. With
p = minFac n, the number k = n^n / p is in the set, since n^n / (n^n / p) = p (the bound noted in
the entry).
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a090525.main := by
  intro n hn
  unfold OMA.S_oeis_a090525.a
  intro h0
  rcases Nat.sInf_eq_zero.mp h0 with h | h
  · simp at h; exact Nat.not_prime_zero h
  · set p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpd : p ∣ n ^ n := dvd_pow (Nat.minFac_dvd n) (by omega)
    have hmem : n ^ n / p ∈ {k : ℕ | (n ^ n / k).Prime} := by
      show (n ^ n / (n ^ n / p)).Prime
      rw [Nat.div_div_self hpd (by positivity)]
      exact hp
    rw [h] at hmem
    exact hmem
