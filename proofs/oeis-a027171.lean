import OMAStatements.S_oeis_a027171
import Mathlib

-- Problem: A027171, R. J. Mathar's affine recurrence for the diagonal term
-- a(n) = C(2n+2, n+1) + C(2n+1, n) + C(2n+1, n+1) + C(2n, n) - 4.
-- Upstream: formal-conjectures statements/oeis-a027171.lean (declaration OMA.S_oeis_a027171.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof: with G(n) = (2n)! / (n! (n+1)!), a(n) = G(n) (9n + 5) - 4 and
-- G(n+1) = G(n) 2(2n+1)/(n+2). Substituting, the recurrence is G(n) times a rational identity in n
-- plus a constant part, both of which vanish identically.

namespace OMA.P_oeis_a027171

open OMA.S_oeis_a027171

noncomputable def G (n : ℕ) : ℚ :=
  ((2 * n).factorial : ℚ) / ((n.factorial : ℚ) * ((n + 1).factorial : ℚ))

noncomputable def rf (x : ℚ) : ℚ := 2 * (2 * x + 1) / (x + 2)

theorem aQ (n : ℕ) : (a n : ℚ) = G n * (9 * (n : ℚ) + 5) - 4 := by
  unfold a G
  push_cast
  rw [Nat.cast_choose ℚ (show n + 1 ≤ 2 * n + 2 by omega), Nat.cast_choose ℚ (show n ≤ 2 * n + 1 by omega),
    Nat.cast_choose ℚ (show n + 1 ≤ 2 * n + 1 by omega), Nat.cast_choose ℚ (show n ≤ 2 * n by omega)]
  rw [show 2 * n + 2 - (n + 1) = n + 1 by omega, show 2 * n + 1 - n = n + 1 by omega,
    show 2 * n + 1 - (n + 1) = n by omega, show 2 * n - n = n by omega]
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem g1 (n : ℕ) : G (n + 1) = G n * rf n := by
  unfold G rf
  rw [show 2 * (n + 1) = 2 * n + 2 by ring]
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n : ℚ) + 1 ≠ 0 := by positivity
  have h4 : (n : ℚ) + 2 ≠ 0 := by positivity
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem hG (x : ℚ) (hx : 0 ≤ x) :
    2 * (x + 3) * (rf x * rf (x + 1) * (9 * (x + 2) + 5)) + (-7 * x - 19) * (rf x * (9 * (x + 1) + 5))
      + 2 * (-2 * x - 1) * (9 * x + 5) = 0 := by
  unfold rf
  have p1 : x + 2 ≠ 0 := by positivity
  have p2 : x + 1 + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem main' : ∀ n : ℕ,
    2 * ((n : ℤ) + 3) * a (n + 2) + (-7 * (n : ℤ) - 19) * a (n + 1) +
      2 * (-2 * (n : ℤ) - 1) * a n + 12 * (-3 * (n : ℤ) - 5) = 0 := by
  intro n
  have h0 := aQ n
  have h1 := aQ (n + 1)
  have h2 := aQ (n + 2)
  have e1 := g1 n
  have e2 := g1 (n + 1)
  have hg := hG (n : ℚ) (by positivity)
  push_cast at h1 h2 e2
  have key : 2 * ((n : ℚ) + 3) * (a (n + 2) : ℚ) + (-7 * (n : ℚ) - 19) * (a (n + 1) : ℚ) +
      2 * (-2 * (n : ℚ) - 1) * (a n : ℚ) + 12 * (-3 * (n : ℚ) - 5) = 0 := by
    rw [h0, h1, h2, e2, e1]
    linear_combination (G n) * hg
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination key

end OMA.P_oeis_a027171

theorem OMA.solution : type_of% @OMA.S_oeis_a027171.main := OMA.P_oeis_a027171.main'
