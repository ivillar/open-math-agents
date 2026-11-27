import OMAStatements.S_oeis_a055008
import Mathlib

/-!
# A055008: terms are squares or twice squares

For k ≥ 3, φ(k) is even, so gcd(φ(k), σ(k)) = 1 forces σ(k) to be odd (the argument noted in the
entry). Write k = 2^a·m with m odd: σ(k) = σ(2^a)σ(m), so σ(m) is odd. For odd m,
σ(p^e) ≡ e + 1 (mod 2) at every odd prime p, so all exponents of m are even and m = s². Hence k
is (2^b s)² or 2(2^b s)² depending on the parity of a; k = 1, 2 are checked directly, and k = 0
has gcd 0.
-/

namespace PA055008
open ArithmeticFunction

theorem geom_odd_mod (p : ℕ) (hp : p % 2 = 1) (N : ℕ) :
    (∑ i ∈ Finset.range N, p ^ i) % 2 = N % 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp, one_pow]
    omega

theorem mod_two_of_mul_left {a b : ℕ} (h : (a * b) % 2 = 1) : a % 2 = 1 := by
  rcases Nat.even_or_odd a with ha | ha
  · have : 2 ∣ a * b := Dvd.dvd.mul_right (even_iff_two_dvd.mp ha) b
    omega
  · exact Nat.odd_iff.mp ha

theorem mod_two_of_mul_right {a b : ℕ} (h : (a * b) % 2 = 1) : b % 2 = 1 := by
  rw [mul_comm] at h
  exact mod_two_of_mul_left h

theorem odd_sigma_square : ∀ m : ℕ, m % 2 = 1 → sigma 1 m % 2 = 1 → ∃ s, m = s ^ 2 := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro hm hs
    rw [sigma_one_apply_prime_pow hp] at hs
    have hp2 : p % 2 = 1 := by
      rcases Nat.even_or_odd p with h | h
      · have : 2 ∣ p ^ n := dvd_pow (even_iff_two_dvd.mp h) hn.ne'
        omega
      · exact Nat.odd_iff.mp h
    rw [geom_odd_mod p hp2] at hs
    obtain ⟨b, rfl⟩ : 2 ∣ n := by omega
    exact ⟨p ^ b, by ring⟩
  | zero => intro hm; simp at hm
  | one => intro _ _; exact ⟨1, rfl⟩
  | coprime a b _ _ hab iha ihb =>
    intro hm hs
    rw [isMultiplicative_sigma.map_mul_of_coprime hab] at hs
    obtain ⟨s, rfl⟩ := iha (mod_two_of_mul_left hm) (mod_two_of_mul_left hs)
    obtain ⟨t, rfl⟩ := ihb (mod_two_of_mul_right hm) (mod_two_of_mul_right hs)
    exact ⟨s * t, by ring⟩

end PA055008

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a055008.main := by
  intro k hk
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · interval_cases k
    · simp at hk
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
  have hphi : Even k.totient := Nat.totient_even (by omega)
  have hs : sigma 1 k % 2 = 1 := by
    rcases Nat.even_or_odd (sigma 1 k) with h | h
    · exfalso
      have h2 : 2 ∣ Nat.gcd k.totient (sigma 1 k) :=
        Nat.dvd_gcd (even_iff_two_dvd.mp hphi) (even_iff_two_dvd.mp h)
      rw [hk] at h2
      omega
    · exact Nat.odd_iff.mp h
  obtain ⟨a, m, hm, hkam⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : k ≠ 0)
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hsk : sigma 1 k = sigma 1 (2 ^ a) * sigma 1 m := by
    rw [hkam, isMultiplicative_sigma.map_mul_of_coprime hcop]
  rw [hsk] at hs
  obtain ⟨s, rfl⟩ := PA055008.odd_sigma_square m (Nat.odd_iff.mp hm) (PA055008.mod_two_of_mul_right hs)
  rcases Nat.even_or_odd a with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · left
    exact ⟨2 ^ b * s, by rw [hkam]; ring⟩
  · right
    exact ⟨2 ^ b * s, by rw [hkam]; ring⟩
