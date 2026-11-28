import OMAStatements.S_oeis_a255163
import Mathlib

-- Problem: A255163, the recurrence a(n) = -12 a(n-1) + 12 a(n-2) and the g.f. -(14x+1)/(12x^2-12x-1)
-- for the irrational parts B(n) of the radii R(n) = A(n) + B(n) sqrt 3.
-- Upstream: formal-conjectures statements/oeis-a255163.lean (declaration OMA.S_oeis_a255163.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (both conjectured parts hold).
-- Proof: eliminate A(n) from the defining pair recursion, then compare coefficients.

namespace OMA.P_oeis_a255163

open OMA.S_oeis_a255163 PowerSeries

theorem rec2 (n : ℕ) : a (n + 2) = -12 * a (n + 1) + 12 * a n := by
  simp only [a, AB]
  ring

theorem a0 : a 0 = 1 := rfl

theorem a1 : a 1 = 2 := by
  simp [a, AB]

theorem key (f : ℚ⟦X⟧) :
    f * (12 * X ^ 2 - 12 * X - 1) = C (12 : ℚ) * (X ^ 2 * f) - C (12 : ℚ) * (X ^ 1 * f) - f := by
  rw [map_ofNat]
  ring

theorem rhs : -(14 * X + 1 : ℚ⟦X⟧) = C (-14 : ℚ) * X ^ 1 - C (1 : ℚ) * X ^ 0 := by
  rw [map_neg, map_ofNat, map_one]
  ring

theorem main' : (∀ n : ℕ, 2 ≤ n → a n = -12 * a (n - 1) + 12 * a (n - 2)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (12 * PowerSeries.X ^ 2 - 12 * PowerSeries.X - 1) =
      -(14 * PowerSeries.X + 1) := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
    exact rec2 k
  · rw [key, rhs]
    ext n
    simp only [map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
    rcases n with _ | _ | n
    · simp [a0]
    · simp [a0, a1]
      norm_num
    · have h := rec2 n
      have h' : ((a (n + 2) : ℤ) : ℚ) = -12 * (a (n + 1) : ℚ) + 12 * (a n : ℚ) := by
        rw [h]
        push_cast
        ring
      simp only [show n + 1 + 1 = n + 2 by omega, if_true, show 1 ≤ n + 2 by omega,
        show 2 ≤ n + 2 by omega, show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega,
        show n + 2 ≠ 1 by omega, show n + 2 ≠ 0 by omega, if_false, h']
      ring

end OMA.P_oeis_a255163

theorem OMA.solution : type_of% @OMA.S_oeis_a255163.main := OMA.P_oeis_a255163.main'
