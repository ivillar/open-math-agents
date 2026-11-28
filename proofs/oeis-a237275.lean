import OMAStatements.S_oeis_a237275
import Mathlib

/-!
Credit: @ivillar
Proof: the set S of admissible k contains k0 = 2^n * t for some t in {1, 2, 3, 4} with last
digit 2 (for n >= 1, 2^n mod 10 is 2, 4, 6 or 8; for n = 0 take k0 = 2), so the least element m
satisfies m <= 4 * 2^n. If the last digit d of m were not 2 it would be at least 3 with
d^n | m, so 3^n <= m <= 4 * 2^n, which is impossible for n >= 4. For n <= 3 the least element
is found by a bounded check over k <= 32.
-/

namespace OMAA237275Helpers

theorem pow_gap (n : ℕ) (hn : 4 ≤ n) : 4 * 2 ^ n < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ, pow_succ]
    omega

end OMAA237275Helpers

open OMAA237275Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a237275.main := by
  intro n
  show sInf {k : ℕ | 0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k} % 10 = 2
  obtain ⟨k0, hk0S, hk0le⟩ : ∃ k0, k0 ∈ {k : ℕ | 0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k} ∧
      k0 ≤ 4 * 2 ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨2, by norm_num, by norm_num⟩
    · have h5 : ¬ 5 ∣ 2 ^ n := fun h => by
        have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h
        omega
      have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      have hp : 0 < 2 ^ n := by positivity
      have hx : 2 ^ n % 10 = 2 ∨ 2 ^ n % 10 = 4 ∨ 2 ^ n % 10 = 6 ∨ 2 ^ n % 10 = 8 := by omega
      have key : ∀ t : ℕ, 0 < t → t ≤ 4 → 2 ^ n * t % 10 = 2 →
          ∃ k0, k0 ∈ {k : ℕ | 0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k} ∧ k0 ≤ 4 * 2 ^ n := by
        intro t ht1 ht4 htd
        refine ⟨2 ^ n * t, ⟨by positivity, by omega, ?_⟩, by nlinarith⟩
        rw [htd]
        exact Dvd.intro t rfl
      rcases hx with hx | hx | hx | hx
      · exact key 1 (by norm_num) (by norm_num) (by omega)
      · exact key 3 (by norm_num) (by norm_num) (by omega)
      · exact key 2 (by norm_num) (by norm_num) (by omega)
      · exact key 4 (by norm_num) (by norm_num) (by omega)
  have hne : ({k : ℕ | 0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k} : Set ℕ).Nonempty := ⟨k0, hk0S⟩
  have hm := Nat.sInf_mem hne
  have hmle := Nat.sInf_le hk0S
  have hmin : ∀ k < sInf {k : ℕ | 0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k},
      ¬ (0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k) := fun k hk => Nat.notMem_of_lt_sInf hk
  generalize sInf {k : ℕ | 0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k} = m at hm hmle hmin ⊢
  obtain ⟨hm0, hm1, hmd⟩ := hm
  rcases Nat.lt_or_ge n 4 with hn | hn
  · have hb : m ≤ 32 := by
      have : 4 * 2 ^ n ≤ 32 := by interval_cases n <;> norm_num
      omega
    have key : ∀ x ≤ 32, (0 < x ∧ 1 < x % 10 ∧ (x % 10) ^ n ∣ x) →
        (∀ k < x, ¬ (0 < k ∧ 1 < k % 10 ∧ (k % 10) ^ n ∣ k)) → x % 10 = 2 := by
      interval_cases n <;> decide +kernel
    exact key m hb ⟨hm0, hm1, hmd⟩ hmin
  · by_contra hd
    have h3 : 3 ≤ m % 10 := by omega
    have h1 : 3 ^ n ≤ (m % 10) ^ n := Nat.pow_le_pow_left h3 n
    have h2 : (m % 10) ^ n ≤ m := Nat.le_of_dvd hm0 hmd
    have := pow_gap n hn
    omega
