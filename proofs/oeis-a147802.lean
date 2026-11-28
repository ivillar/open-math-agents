import OMAStatements.S_oeis_a147802
import Mathlib

-- Problem: a147802, rad(m (3^n - m) 3^n) = 3 rad(m (3^n - m)) for m coprime to 3 with m < 3^n.
-- Upstream: formal-conjectures statements/oeis-a147802.lean (declaration OMA.S_oeis_a147802.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the remark in the entry holds; it is an elementary fact).
-- Proof: n >= 1 since m >= 1. 3 does not divide 3^n - m (else it would divide m), so
-- m (3^n - m) is coprime to 3^n; the radical is multiplicative on coprime factors and
-- rad(3^n) = 3.

namespace OMA.P_oeis_a147802

open OMA.S_oeis_a147802 UniqueFactorizationMonoid

theorem main' : ∀ n m : ℕ, Nat.Coprime m 3 → m < 3 ^ n →
      radical (m * (3 ^ n - m) * 3 ^ n) = 3 * radical (m * (3 ^ n - m)) := by
  intro n m hm hlt
  have hp : Nat.Prime 3 := by norm_num
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hlt
    exact hm0 hlt
  have hnd : ¬ 3 ∣ m := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp] at hm
    exact hm
  have h3 : Nat.Coprime (3 ^ n - m) 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    apply hnd
    obtain ⟨c, hc⟩ := hd
    obtain ⟨d, hd'⟩ := dvd_pow_self 3 hn
    refine ⟨d - c, ?_⟩
    rw [Nat.mul_sub]
    omega
  have hx : Nat.Coprime (m * (3 ^ n - m)) (3 ^ n) :=
    Nat.Coprime.pow_right n (Nat.Coprime.mul_left hm h3)
  rw [radical_mul (Nat.coprime_iff_isRelPrime.mp hx), radical_pow_of_prime hp.prime hn]
  simp [mul_comm]

end OMA.P_oeis_a147802

theorem OMA.solution : type_of% @OMA.S_oeis_a147802.main := OMA.P_oeis_a147802.main'
