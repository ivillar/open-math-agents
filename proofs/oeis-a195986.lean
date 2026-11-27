import OMAStatements.S_oeis_a195986
import Mathlib

/-!
# A195986: the 2-adic valuation of 5^n − 3^n

For odd n, 5^n ≡ 1 and 3^n ≡ 3 (mod 4), so 5^n − 3^n and 3^n − 1 are both ≡ 2 (mod 4) and have
valuation 1. For even n, the lifting-the-exponent lemma (Mathlib's `padicValNat.pow_two_sub_pow`)
gives v₂(5^n − 3^n) = v₂(8) + v₂(2) + v₂(n) − 1 = 3 + v₂(n) and v₂(3^n − 1) = 2 + v₂(n) ≥ 3, so the
first is the second plus one.
-/

namespace PA195986

theorem val_of_mod4 (x : ℕ) (h : x % 4 = 2) : padicValNat 2 x = 1 := by
  have hx : x = 2 * (x / 2) := by omega
  have hodd : ¬ 2 ∣ x / 2 := by omega
  rw [hx, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd hodd]

end PA195986

theorem OMA.solution : type_of% @OMA.S_oeis_a195986.main := by
  intro n hn
  unfold OMA.S_oeis_a195986.a OMA.S_oeis_a195986.b
  rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have hn0 : t + t ≠ 0 := by omega
    have he : Even (t + t) := ⟨t, rfl⟩
    have h1 := padicValNat.pow_two_sub_pow (x := 5) (y := 3) (by norm_num) (by norm_num)
      (by norm_num) hn0 he
    have h2 := padicValNat.pow_two_sub_pow (x := 3) (y := 1) (by norm_num) (by norm_num)
      (by norm_num) hn0 he
    rw [one_pow] at h2
    have v8 : padicValNat 2 (5 + 3) = 3 := by
      rw [show 5 + 3 = 2 ^ 3 by norm_num, padicValNat.prime_pow]
    have v2 : padicValNat 2 (5 - 3) = 1 := by
      rw [show 5 - 3 = 2 by norm_num, padicValNat.self (by norm_num)]
    have v4 : padicValNat 2 (3 + 1) = 2 := by
      rw [show 3 + 1 = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have v2' : padicValNat 2 (3 - 1) = 1 := by
      rw [show 3 - 1 = 2 by norm_num, padicValNat.self (by norm_num)]
    rw [v8, v2] at h1
    rw [v4, v2'] at h2
    rw [if_neg (by omega)]
    omega
  · have h5 : 5 ^ (2 * t + 1) % 4 = 1 := by
      rw [Nat.pow_mod]; norm_num
    have h3 : 3 ^ (2 * t + 1) % 4 = 3 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
    have hle : 3 ^ (2 * t + 1) ≤ 5 ^ (2 * t + 1) := Nat.pow_le_pow_left (by norm_num) _
    have hpos : 1 ≤ 3 ^ (2 * t + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hA : (5 ^ (2 * t + 1) - 3 ^ (2 * t + 1)) % 4 = 2 := by
      generalize 5 ^ (2 * t + 1) = A at h5 hle ⊢
      generalize 3 ^ (2 * t + 1) = B at h3 hle ⊢
      omega
    have hB : (3 ^ (2 * t + 1) - 1) % 4 = 2 := by
      generalize 3 ^ (2 * t + 1) = B at h3 hpos ⊢
      omega
    rw [PA195986.val_of_mod4 _ hA, PA195986.val_of_mod4 _ hB, if_pos rfl]
