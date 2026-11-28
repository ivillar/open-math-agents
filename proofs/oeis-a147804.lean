import OMAStatements.S_oeis_a147804
import Mathlib

-- Problem: a147804, rad(m (7^n - m) 7^n) = 7 rad(m (7^n - m)) for m coprime to 7 with m < 7^n.
-- Upstream: formal-conjectures statements/oeis-a147804.lean (declaration OMA.S_oeis_a147804.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the remark in the entry holds; it is an elementary fact).
-- Proof: n >= 1 since m >= 1. 7 does not divide 7^n - m (else it would divide m), so
-- m (7^n - m) is coprime to 7^n; the radical is multiplicative on coprime factors and
-- rad(7^n) = 7.

namespace OMA.P_oeis_a147804

open OMA.S_oeis_a147804 UniqueFactorizationMonoid

theorem main' : ∀ n m : ℕ, Nat.Coprime m 7 → m < 7 ^ n →
      radical (m * (7 ^ n - m) * 7 ^ n) = 7 * radical (m * (7 ^ n - m)) := by
  intro n m hm hlt
  have hp : Nat.Prime 7 := by norm_num
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hlt
    exact hm0 hlt
  have hnd : ¬ 7 ∣ m := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp] at hm
    exact hm
  have h3 : Nat.Coprime (7 ^ n - m) 7 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    apply hnd
    obtain ⟨c, hc⟩ := hd
    obtain ⟨d, hd'⟩ := dvd_pow_self 7 hn
    refine ⟨d - c, ?_⟩
    rw [Nat.mul_sub]
    omega
  have hx : Nat.Coprime (m * (7 ^ n - m)) (7 ^ n) :=
    Nat.Coprime.pow_right n (Nat.Coprime.mul_left hm h3)
  rw [radical_mul (Nat.coprime_iff_isRelPrime.mp hx), radical_pow_of_prime hp.prime hn]
  simp [mul_comm]

end OMA.P_oeis_a147804

theorem OMA.solution : type_of% @OMA.S_oeis_a147804.main := OMA.P_oeis_a147804.main'
