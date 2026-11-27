import OMAStatements.S_oeis_a192252
import Mathlib

-- Problem: A192252, constant term of the reduction of sum k! x^k by x^2 -> x+1; the recurrence.
-- Upstream: formal-conjectures statements/oeis-a192252.lean (declaration OMA.S_oeis_a192252.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: x^k reduces to F(k) x + (F(k+1) - F(k)) modulo x^2 - x - 1, so
-- a(n) = sum_{k<=n} k! (F(k+1) - F(k)); the stated recurrence then reduces to
-- (m+3)! (F(m+2) - F(m+1) - F(m)) = 0.

namespace OMA.P_oeis_a192252

open OMA.S_oeis_a192252 Polynomial

/-- The modulus `x^2 - x - 1`. -/
noncomputable def q : ℤ[X] := X ^ 2 - X - 1

theorem q_monic : q.Monic := by
  unfold q
  have : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + 1) := by ring
  rw [this]
  apply Polynomial.monic_X_pow_sub
  have h : (X + 1 : ℤ[X]).degree ≤ 1 := by compute_degree
  exact lt_of_le_of_lt h (by norm_num)

/-- The linear remainder of `x^k`. -/
noncomputable def r (k : ℕ) : ℤ[X] :=
  C (Nat.fib k : ℤ) * X + C ((Nat.fib (k + 1) : ℤ) - Nat.fib k)

theorem q_dvd_pow (k : ℕ) : q ∣ X ^ k - r k := by
  induction k with
  | zero => exact ⟨0, by simp [r]⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨X * c + C (Nat.fib k : ℤ), ?_⟩
    have hf : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    have e : X ^ (k + 1) - r (k + 1) = X * (X ^ k - r k) + C (Nat.fib k : ℤ) * q := by
      unfold r q
      rw [hf]
      simp only [map_sub, map_add]
      ring
    rw [e, hc]
    ring

/-- The remainder of `p n`. -/
noncomputable def R (n : ℕ) : ℤ[X] := ∑ k ∈ Finset.range (n + 1), C (k.factorial : ℤ) * r k

theorem R_eq (n : ℕ) : R n = C (∑ k ∈ Finset.range (n + 1), (k.factorial : ℤ) * Nat.fib k) * X +
    C (∑ k ∈ Finset.range (n + 1), (k.factorial : ℤ) * ((Nat.fib (k + 1) : ℤ) - Nat.fib k)) := by
  unfold R r
  rw [map_sum, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [map_mul]
  ring

theorem a_eq (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), (k.factorial : ℤ) * ((Nat.fib (k + 1) : ℤ) - Nat.fib k) := by
  unfold a
  have h1 : p n %ₘ q = R n %ₘ q := by
    apply Polynomial.modByMonic_eq_of_dvd_sub q_monic
    unfold p R
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro k _
    rw [← mul_sub]
    exact Dvd.dvd.mul_left (q_dvd_pow k) _
  have h2 : R n %ₘ q = R n := by
    rw [Polynomial.modByMonic_eq_self_iff q_monic]
    have hq : q.degree = 2 := by
      unfold q
      compute_degree!
    rw [hq, R_eq]
    calc (C _ * X + C _ : ℤ[X]).degree ≤ 1 := by compute_degree
      _ < 2 := by norm_num
  have hqdef : (X ^ 2 - X - 1 : ℤ[X]) = q := rfl
  rw [hqdef, h1, h2, R_eq]
  simp

theorem main' : ∀ n : ℕ, 3 ≤ n →
    a n + (-(n : ℤ) - 1) * a (n - 1) - (n : ℤ) * ((n : ℤ) - 2) * a (n - 2)
      + (n : ℤ) * ((n : ℤ) - 1) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega, a_eq, a_eq, a_eq, a_eq]
  rw [Finset.sum_range_succ _ (m + 3), Finset.sum_range_succ _ (m + 2),
    Finset.sum_range_succ _ (m + 1)]
  have f2 : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
    rw [Nat.fib_add_two]; push_cast; ring
  have f3 : (Nat.fib (m + 3) : ℤ) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
    rw [Nat.fib_add_two]; push_cast; ring
  have f4 : (Nat.fib (m + 4) : ℤ) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
    rw [Nat.fib_add_two]; push_cast; ring
  rw [show m + 3 + 1 = m + 4 by ring, show m + 2 + 1 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring,
    f4, f3, f2, Nat.factorial_succ (m + 2), Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  push_cast
  ring

end OMA.P_oeis_a192252

theorem OMA.solution : type_of% @OMA.S_oeis_a192252.main := OMA.P_oeis_a192252.main'
