import OMAStatements.S_oeis_a381005
import Mathlib

/-!
# A381005: the triangles are primitive

B + C = 2^(4n+1) (no truncation in B, since 2^(4n−2) + 2^(2n) + 1 ≤ 2^(4n) for n ≥ 1), and C is odd.
A common divisor of A, B, C divides B + C, a power of 2, and the odd number C, so it is 1.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a381005.main := by
  intro n hn
  have hu : 2 ^ (4 * n) = 4 * 2 ^ (4 * n - 2) := by
    have : 2 ^ (4 * n) = 2 ^ 2 * 2 ^ (4 * n - 2) := by rw [← pow_add]; congr 1; omega
    rw [this]; norm_num
  have hv : 2 ^ (2 * n) ≤ 2 ^ (4 * n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hw : 1 ≤ 2 ^ (4 * n - 2) := Nat.one_le_two_pow
  have hBC : OMA.S_oeis_a381005.B n + OMA.S_oeis_a381005.C n = 2 ^ (4 * n + 1) := by
    unfold OMA.S_oeis_a381005.B OMA.S_oeis_a381005.C
    rw [pow_succ]
    omega
  have e1 : 2 ∣ 2 ^ (4 * n) := dvd_pow_self 2 (by omega)
  have e2 : 2 ∣ 2 ^ (4 * n - 2) := dvd_pow_self 2 (by omega)
  have e3 : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
  have hCodd : Odd (OMA.S_oeis_a381005.C n) := by
    unfold OMA.S_oeis_a381005.C
    rw [Nat.odd_iff]
    omega
  have hcop : Nat.Coprime (OMA.S_oeis_a381005.C n) (2 ^ (4 * n + 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hCodd)
  set d := Nat.gcd (Nat.gcd (OMA.S_oeis_a381005.A n) (OMA.S_oeis_a381005.B n)) (OMA.S_oeis_a381005.C n)
  have hdB : d ∣ OMA.S_oeis_a381005.B n := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hdC : d ∣ OMA.S_oeis_a381005.C n := Nat.gcd_dvd_right _ _
  have hd2 : d ∣ 2 ^ (4 * n + 1) := by rw [← hBC]; exact dvd_add hdB hdC
  have := Nat.dvd_gcd hdC hd2
  rw [hcop.gcd_eq_one] at this
  exact Nat.eq_one_of_dvd_one this
