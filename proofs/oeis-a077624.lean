import OMAStatements.S_oeis_a077624
import Mathlib

-- Problem: A077624, 2^n + 1 is a perfect square only for n = 3.
-- Upstream: formal-conjectures statements/oeis-a077624.lean (declaration OMA.S_oeis_a077624.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (a classical fact). Proof: 2^n = (m-1)(m+1) makes both factors powers of 2
-- that differ by 2, hence 2 and 4, so m = 3 and n = 3.

namespace OMA.P_oeis_a077624

open OMA.S_oeis_a077624

theorem main' : ∀ n : ℕ, IsSquare (2 ^ n + 1) ↔ n = 3 := by
  intro n
  constructor
  · rintro ⟨m, hm⟩
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h] at hm; simp at hm
      · exact h
    have hprod : (m - 1) * (m + 1) = 2 ^ n := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith [hm]
    have h1 : m - 1 ∣ 2 ^ n := ⟨m + 1, hprod.symm⟩
    have h2 : m + 1 ∣ 2 ^ n := ⟨m - 1, by rw [← hprod]; ring⟩
    obtain ⟨a, ha, hae⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    obtain ⟨b, hb, hbe⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    have hab : 2 ^ b = 2 ^ a + 2 := by omega
    have ha1 : a = 1 := by
      rcases Nat.lt_trichotomy a 1 with h | h | h
      · have : a = 0 := by omega
        subst this
        rcases b with _ | b
        · norm_num at hab
        · rw [pow_succ] at hab
          norm_num at hab
          omega
      · exact h
      · exfalso
        have hb2 : 2 ≤ b := by
          by_contra hc
          have : 2 ^ b ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have h4a : 4 ∣ 2 ^ a := by
          rw [show a = 2 + (a - 2) by omega, pow_add]; exact Dvd.intro _ rfl
        have h4b : 4 ∣ 2 ^ b := by
          rw [show b = 2 + (b - 2) by omega, pow_add]; exact Dvd.intro _ rfl
        omega
    subst ha1
    have hm3 : m = 3 := by simp at hae; omega
    subst hm3
    have h8 : 2 ^ n = 2 ^ 3 := by omega
    exact Nat.pow_right_injective (le_refl 2) h8
  · rintro rfl
    exact ⟨3, by norm_num⟩

end OMA.P_oeis_a077624

theorem OMA.solution : type_of% @OMA.S_oeis_a077624.main := OMA.P_oeis_a077624.main'
