import OMAStatements.S_oeis_a077625
import Mathlib

/-!
Credit: @ivillar
Proof: 2^1 - 1 = 1 is a square. For n >= 2, 4 divides 2^n, so 2^n - 1 is 3 modulo 4, while
every square is 0 or 1 modulo 4.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a077625.main := by
  intro n hn
  constructor
  · rintro ⟨r, hr⟩
    by_contra hne
    have h2 : 2 ≤ n := by omega
    have h4 : 4 ∣ 2 ^ n := by
      have := pow_dvd_pow 2 h2
      norm_num at this
      exact this
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hmod : (2 ^ n - 1) % 4 = 3 := by omega
    rw [hr] at hmod
    have hr4 : r * r % 4 = (r % 4) * (r % 4) % 4 := Nat.mul_mod r r 4
    have hlt : r % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hh : r % 4 <;> omega
  · rintro rfl
    exact ⟨1, by norm_num⟩
