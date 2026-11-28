import OMAStatements.S_oeis_a192431
import Mathlib

-- Problem: A192431, the recurrence a(n) = 2a(n-1) + 6a(n-2) - 2a(n-3) - a(n-4) for the coefficient
-- of x in the reduction of p(n,x) by x^2 -> x + 1.
-- Upstream: formal-conjectures statements/oeis-a192431.lean (declaration OMA.S_oeis_a192431.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated recurrence holds for n > 3).
-- Proof: p(n+2) = 2x p(n+1) - (x^2 - x - 2) p(n); track the remainder u(n) + v(n) x modulo
-- x^2 - x - 1 and eliminate u.

namespace OMA.P_oeis_a192431

open OMA.S_oeis_a192431 Polynomial

/-- The remainder of p(n) modulo x^2 - x - 1, as the pair (constant term, coefficient of x). -/
def uv : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (1, 1)
  | n + 2 => ((uv n).1 + 2 * (uv (n + 1)).2, 2 * (uv (n + 1)).1 + 2 * (uv (n + 1)).2 + (uv n).2)

theorem p_rec (n : ℕ) : p (n + 2) = 2 * X * p (n + 1) - (X ^ 2 - X - 2) * p n := by
  have h1 : (pq (n + 2)).1 = X * (pq (n + 1)).1 + (X + 2) * (pq (n + 1)).2 := rfl
  have h2 : (pq (n + 2)).2 = (pq (n + 1)).1 + X * (pq (n + 1)).2 := rfl
  have h3 : (pq (n + 1)).1 = X * (pq n).1 + (X + 2) * (pq n).2 := rfl
  have h4 : (pq (n + 1)).2 = (pq n).1 + X * (pq n).2 := rfl
  simp only [p]
  linear_combination h1 + (X + 2) * h4 - X * h3 + h2 + h3 - X * h4

theorem rem (n : ℕ) :
    (∃ h : ℤ[X], p n = C (uv n).2 * X + C (uv n).1 + (X ^ 2 - X - 1) * h) ∧
      ∃ h : ℤ[X], p (n + 1) = C (uv (n + 1)).2 * X + C (uv (n + 1)).1 + (X ^ 2 - X - 1) * h := by
  induction n with
  | zero =>
    refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
    · simp [p, pq, uv]
    · simp [p, pq, uv]
  | succ n ih =>
    obtain ⟨⟨h0, e0⟩, ⟨h1, e1⟩⟩ := ih
    refine ⟨⟨h1, e1⟩, ⟨2 * X * h1 + 2 * C (uv (n + 1)).2 - (C (uv n).2 * X + C (uv n).1 + (X ^ 2 - X - 1) * h0) + h0, ?_⟩⟩
    have hp := p_rec n
    have hu : uv (n + 2) = ((uv n).1 + 2 * (uv (n + 1)).2,
        2 * (uv (n + 1)).1 + 2 * (uv (n + 1)).2 + (uv n).2) := rfl
    rw [hu]
    simp only [map_add, map_mul, map_ofNat]
    linear_combination hp + 2 * X * e1 - (X ^ 2 - X - 2) * e0

theorem monic_g : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + 1) := by ring
  rw [this]
  apply monic_X_pow_sub
  compute_degree!

theorem deg_g : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by
  compute_degree!

theorem a_eq (n : ℕ) : a n = (uv n).2 := by
  obtain ⟨⟨h, e⟩, -⟩ := rem n
  have hm := (div_modByMonic_unique (f := p n) h (C (uv n).2 * X + C (uv n).1) monic_g
    ⟨e.symm, by rw [deg_g]; exact degree_linear_lt⟩).2
  simp only [a, hm, coeff_add, coeff_C_mul_X, coeff_C]
  simp

theorem v_rec (n : ℕ) :
    (uv (n + 4)).2 = 2 * (uv (n + 3)).2 + 6 * (uv (n + 2)).2 - 2 * (uv (n + 1)).2 - (uv n).2 := by
  have e1 : (uv (n + 4)).2 = 2 * (uv (n + 3)).1 + 2 * (uv (n + 3)).2 + (uv (n + 2)).2 := rfl
  have e2 : (uv (n + 3)).1 = (uv (n + 1)).1 + 2 * (uv (n + 2)).2 := rfl
  have e3 : (uv (n + 2)).2 = 2 * (uv (n + 1)).1 + 2 * (uv (n + 1)).2 + (uv n).2 := rfl
  linear_combination e1 + 2 * e2 - e3

theorem main' : ∀ n : ℕ, 3 < n →
    a n = 2 * a (n - 1) + 6 * a (n - 2) - 2 * a (n - 3) - a (n - 4) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  simp only [a_eq]
  exact v_rec k

end OMA.P_oeis_a192431

theorem OMA.solution : type_of% @OMA.S_oeis_a192431.main := OMA.P_oeis_a192431.main'
