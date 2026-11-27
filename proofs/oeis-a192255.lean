import OMAStatements.S_oeis_a192255
import Mathlib

/-!
Credit: @ivillar
Proof: with g = x^2 - x - 1, g divides x^(i+1) - (F(i+1) x + F(i)) (induction on i, using
x * (x^(i+1) - F(i+1) x - F(i)) + F(i+1) g = x^(i+2) - F(i+2) x - F(i+1)), so the remainder of
x^(i+1) mod g is F(i+1) x + F(i), whose coefficient of x is F(i+1). The remainder map is linear
and p(n) = Sum_{i=0..n} (i+1)^2 x^i, so the coefficient of x of p(n) mod g is
Sum_{i=0..n} (i+1)^2 F(i) = Sum_{i=1..n+1} i^2 F(i-1).
-/

namespace OMAA192255Helpers
open Polynomial OMA.S_oeis_a192255

theorem hg : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!

theorem hdeg : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by compute_degree!

theorem dvd (i : ℕ) : (X ^ 2 - X - 1 : ℤ[X]) ∣
    X ^ (i + 1) - (C (Nat.fib (i + 1) : ℤ) * X + C (Nat.fib i : ℤ)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    obtain ⟨q, hq⟩ := ih
    have e : C (Nat.fib (i + 2) : ℤ) = C (Nat.fib i : ℤ) + C (Nat.fib (i + 1) : ℤ) := by
      rw [Nat.fib_add_two, Nat.cast_add, C_add]
    refine ⟨X * q + C (Nat.fib (i + 1) : ℤ), ?_⟩
    rw [show i + 1 + 1 = i + 2 by ring]
    linear_combination X * hq - X * e

theorem rem (i : ℕ) : X ^ (i + 1) %ₘ (X ^ 2 - X - 1 : ℤ[X]) =
    C (Nat.fib (i + 1) : ℤ) * X + C (Nat.fib i : ℤ) := by
  rw [modByMonic_eq_of_dvd_sub hg (dvd i), (modByMonic_eq_self_iff hg).mpr]
  exact lt_of_le_of_lt degree_linear_le (by rw [hdeg]; decide)

theorem one_rem : (1 : ℤ[X]) %ₘ (X ^ 2 - X - 1 : ℤ[X]) = 1 :=
  (modByMonic_eq_self_iff hg).mpr (by rw [hdeg, degree_one]; decide)

theorem coeff_main (n : ℕ) : (p n %ₘ (X ^ 2 - X - 1)).coeff 1 =
    ∑ i ∈ Finset.range (n + 1), ((i : ℤ) + 1) ^ 2 * (Nat.fib i : ℤ) := by
  induction n with
  | zero =>
    show ((1 : ℤ[X]) %ₘ (X ^ 2 - X - 1)).coeff 1 = _
    rw [one_rem]
    simp [Polynomial.coeff_one]
  | succ n ih =>
    show ((p n + X ^ (n + 1) * C (((n : ℤ) + 2) ^ 2)) %ₘ (X ^ 2 - X - 1)).coeff 1 = _
    rw [add_modByMonic, mul_comm (X ^ (n + 1)), ← smul_eq_C_mul, smul_modByMonic, rem,
      coeff_add, coeff_smul, ih, Finset.sum_range_succ _ (n + 1)]
    have h1 : (C (Nat.fib (n + 1) : ℤ) * X + C (Nat.fib n : ℤ)).coeff 1 =
        (Nat.fib (n + 1) : ℤ) := by
      simp
    rw [h1, smul_eq_mul]
    push_cast
    ring

theorem hs (m : ℕ) : ∑ i ∈ Finset.Icc 1 (m + 1), (i : ℤ) ^ 2 * (Nat.fib (i - 1) : ℤ) =
    ∑ i ∈ Finset.range (m + 1), ((i : ℤ) + 1) ^ 2 * (Nat.fib i : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ m + 1 + 1 by omega), ih, Finset.sum_range_succ _ (m + 1),
      show m + 1 + 1 - 1 = m + 1 by omega]
    push_cast
    ring

end OMAA192255Helpers

open OMAA192255Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a192255.main := by
  intro n
  unfold OMA.S_oeis_a192255.a
  rw [show n + 1 - 1 = n by omega, coeff_main, hs n]
