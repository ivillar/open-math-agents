import OMAStatements.S_oeis_a027175
import Mathlib

-- Problem: A027175, R. J. Mathar's affine recurrence for the diagonal term
-- a(n) = C(2n+3, n+1) + C(2n+2, n) + C(2n+2, n+1) + C(2n+1, n) - 4.
-- Upstream: formal-conjectures statements/oeis-a027175.lean (declaration OMA.S_oeis_a027175.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof: with G(n) = (2n+1)! / (n! (n+2)!), a(n) = G(n) (9n + 14) - 4 and
-- G(n+1) = G(n) 2(2n+3)/(n+3). Substituting, the recurrence is G(n) times a rational identity in n
-- plus a constant part, both of which vanish identically.

namespace OMA.P_oeis_a027175

open OMA.S_oeis_a027175

noncomputable def G (n : ℕ) : ℚ :=
  ((2 * n + 1).factorial : ℚ) / ((n.factorial : ℚ) * ((n + 2).factorial : ℚ))

noncomputable def rf (x : ℚ) : ℚ := 2 * (2 * x + 3) / (x + 3)

theorem aQ (n : ℕ) : (a n : ℚ) = G n * (9 * (n : ℚ) + 14) - 4 := by
  unfold a G
  push_cast
  rw [Nat.cast_choose ℚ (show n + 1 ≤ 2 * n + 3 by omega), Nat.cast_choose ℚ (show n ≤ 2 * n + 2 by omega),
    Nat.cast_choose ℚ (show n + 1 ≤ 2 * n + 2 by omega), Nat.cast_choose ℚ (show n ≤ 2 * n + 1 by omega)]
  rw [show 2 * n + 3 - (n + 1) = n + 2 by omega, show 2 * n + 2 - n = n + 2 by omega,
    show 2 * n + 2 - (n + 1) = n + 1 by omega, show 2 * n + 1 - n = n + 1 by omega]
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem g1 (n : ℕ) : G (n + 1) = G n * rf n := by
  unfold G rf
  rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring, show n + 1 + 2 = n + 3 by ring]
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n : ℚ) + 1 ≠ 0 := by positivity
  have h4 : (n : ℚ) + 3 ≠ 0 := by positivity
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem hG (x : ℚ) (hx : 0 ≤ x) :
    2 * (x + 4) * (rf x * rf (x + 1) * (9 * (x + 2) + 14)) + (-7 * x - 26) * (rf x * (9 * (x + 1) + 14))
      + 2 * (-2 * x - 3) * (9 * x + 14) = 0 := by
  unfold rf
  have p1 : x + 3 ≠ 0 := by positivity
  have p2 : x + 1 + 3 ≠ 0 := by positivity
  field_simp
  ring

theorem main' : ∀ n : ℕ,
    2 * ((n : ℤ) + 4) * a (n + 2) + (-7 * (n : ℤ) - 26) * a (n + 1) +
      2 * (-2 * (n : ℤ) - 3) * a n + 12 * (-3 * (n : ℤ) - 8) = 0 := by
  intro n
  have h0 := aQ n
  have h1 := aQ (n + 1)
  have h2 := aQ (n + 2)
  have e1 := g1 n
  have e2 := g1 (n + 1)
  have hg := hG (n : ℚ) (by positivity)
  push_cast at h1 h2 e2
  have key : 2 * ((n : ℚ) + 4) * (a (n + 2) : ℚ) + (-7 * (n : ℚ) - 26) * (a (n + 1) : ℚ) +
      2 * (-2 * (n : ℚ) - 3) * (a n : ℚ) + 12 * (-3 * (n : ℚ) - 8) = 0 := by
    rw [h0, h1, h2, e2, e1]
    linear_combination (G n) * hg
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination key

end OMA.P_oeis_a027175

theorem OMA.solution : type_of% @OMA.S_oeis_a027175.main := OMA.P_oeis_a027175.main'
