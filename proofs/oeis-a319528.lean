import OMAStatements.S_oeis_a319528
import Mathlib

/-!
# A319528: σ(7n) = 8σ(n) exactly when 7 ∤ n

If 7 ∤ n, σ is multiplicative and σ(7) = 8. If n = 7^e·m with e ≥ 1 and 7 ∤ m, then
σ(7n) = σ(7^(e+1))σ(m) = (7σ(7^e) + 1)σ(m), while 8σ(n) = 8σ(7^e)σ(m); equality would force
σ(7^e) = 1, but σ(7^e) ≥ 8 (the multiplicativity argument in the entry).
-/

namespace PA319528
open ArithmeticFunction

theorem sigma_pow_succ (e : ℕ) : sigma 1 (7 ^ (e + 1)) = 7 * sigma 1 (7 ^ e) + 1 := by
  rw [sigma_one_apply_prime_pow (by norm_num), sigma_one_apply_prime_pow (by norm_num),
    Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sigma_pow_ge (e : ℕ) (he : 1 ≤ e) : 8 ≤ sigma 1 (7 ^ e) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [sigma_pow_succ]
  have : 1 ≤ sigma 1 (7 ^ k) := (sigma_pos_iff).mpr (by positivity)
  omega

end PA319528

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a319528.main := by
  intro n hn
  constructor
  · intro h h7
    obtain ⟨e, m, hm7, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 7 (by norm_num)
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | he
      · simp at h7; exact absurd h7 hm7
      · exact he
    have hcop : ∀ k, Nat.Coprime (7 ^ k) m := fun k =>
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm7)
    rw [← mul_assoc, ← pow_succ', isMultiplicative_sigma.map_mul_of_coprime (hcop _),
      isMultiplicative_sigma.map_mul_of_coprime (hcop _), PA319528.sigma_pow_succ] at h
    have hm : 0 < sigma 1 m := (sigma_pos_iff).mpr (by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at hm7
      · exact hm)
    have h' : (7 * sigma 1 (7 ^ e) + 1) * sigma 1 m = (8 * sigma 1 (7 ^ e)) * sigma 1 m := by
      rw [h]; ring
    have := Nat.eq_of_mul_eq_mul_right hm h'
    have := PA319528.sigma_pow_ge e he
    omega
  · intro h7
    have hcop : Nat.Coprime 7 n := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
    congr 1
