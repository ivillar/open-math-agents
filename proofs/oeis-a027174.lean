import OMAStatements.S_oeis_a027174
import Mathlib

-- Problem: A027174, R. J. Mathar's affine recurrence for the diagonal term
-- a(n) = C(2n+6, n+1) + C(2n+5, n) + C(2n+5, n+1) + C(2n+4, n) - 4.
-- Upstream: formal-conjectures statements/oeis-a027174.lean (declaration OMA.S_oeis_a027174.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof idea: with G(n) = (2n+4)! / (n! (n+5)!), each binomial is G(n) times a rational function
-- of n, so a(n) = G(n) h(n) - 4, and G(n+1) = G(n) (2n+6)(2n+5) / ((n+1)(n+6)). Substituting,
-- the recurrence becomes an identity of rational functions in n (times G(n)) plus a constant part,
-- both of which vanish identically.

namespace OMA.P_oeis_a027174

open OMA.S_oeis_a027174

noncomputable def G (n : ℕ) : ℚ :=
  ((2 * n + 4).factorial : ℚ) / ((n.factorial : ℚ) * ((n + 5).factorial : ℚ))

noncomputable def Hf (x : ℚ) : ℚ := (9 * x ^ 2 + 50 * x + 65) / (x + 1)

noncomputable def rf (x : ℚ) : ℚ := (2 * x + 6) * (2 * x + 5) / ((x + 1) * (x + 6))

theorem aQ (n : ℕ) : (a n : ℚ) = G n * Hf n - 4 := by
  unfold a G Hf
  push_cast
  rw [Nat.cast_choose ℚ (show n + 1 ≤ 2 * n + 6 by omega), Nat.cast_choose ℚ (show n ≤ 2 * n + 5 by omega),
    Nat.cast_choose ℚ (show n + 1 ≤ 2 * n + 5 by omega), Nat.cast_choose ℚ (show n ≤ 2 * n + 4 by omega)]
  rw [show 2 * n + 6 - (n + 1) = n + 5 by omega, show 2 * n + 5 - n = n + 5 by omega,
    show 2 * n + 5 - (n + 1) = n + 4 by omega, show 2 * n + 4 - n = n + 4 by omega]
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem g1 (n : ℕ) : G (n + 1) = G n * rf n := by
  unfold G rf
  rw [show 2 * (n + 1) + 4 = 2 * n + 6 by ring, show n + 1 + 5 = n + 6 by ring]
  have h1 : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n : ℚ) + 1 ≠ 0 := by positivity
  have h4 : (n : ℚ) + 6 ≠ 0 := by positivity
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem hG (x : ℚ) (hx : 0 ≤ x) :
    -2 * ((x + 4) + 3) * (139 * (x + 4) - 175) * (rf x * rf (x + 1) * Hf (x + 2)) +
      (1279 * (x + 4) ^ 2 + 1334 * (x + 4) - 1089) * (rf x * Hf (x + 1)) -
      2 * (167 * (x + 4) + 121) * (2 * (x + 4) - 3) * Hf x = 0 := by
  unfold rf Hf
  have p1 : x + 1 ≠ 0 := by positivity
  have p2 : x + 1 + 1 ≠ 0 := by positivity
  have p3 : x + 6 ≠ 0 := by positivity
  have p4 : x + 1 + 6 ≠ 0 := by positivity
  have p5 : x + 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem main' : ∀ n : ℕ,
    let m := (n : ℤ) + 4;
    -2 * (m + 3) * (139 * m - 175) * a (n + 2) +
      (1279 * m ^ 2 + 1334 * m - 1089) * a (n + 1) -
      2 * (167 * m + 121) * (2 * m - 3) * a n +
      12 * (111 * m ^ 2 + 456 * m + 229) = 0 := by
  intro n
  dsimp only
  have h0 := aQ n
  have h1 := aQ (n + 1)
  have h2 := aQ (n + 2)
  have e1 := g1 n
  have e2 := g1 (n + 1)
  have hg := hG (n : ℚ) (by positivity)
  push_cast at h1 h2 e2
  have key : -2 * (((n : ℚ) + 4) + 3) * (139 * ((n : ℚ) + 4) - 175) * (a (n + 2) : ℚ) +
      (1279 * ((n : ℚ) + 4) ^ 2 + 1334 * ((n : ℚ) + 4) - 1089) * (a (n + 1) : ℚ) -
      2 * (167 * ((n : ℚ) + 4) + 121) * (2 * ((n : ℚ) + 4) - 3) * (a n : ℚ) +
      12 * (111 * ((n : ℚ) + 4) ^ 2 + 456 * ((n : ℚ) + 4) + 229) = 0 := by
    rw [h0, h1, h2, e2, e1]
    linear_combination (G n) * hg
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination key

end OMA.P_oeis_a027174

theorem OMA.solution : type_of% @OMA.S_oeis_a027174.main := OMA.P_oeis_a027174.main'
