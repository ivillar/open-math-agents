import OMAStatements.S_oeis_a309717
import Mathlib

-- Problem: A309717, 2 a(n) = F_1(n) - 2 F_2(n) + F_3(n) for the coefficients a(n) of the product of the
-- generating functions of the Fibonacci polynomial sequences with t = 1, 2, 3.
-- Upstream: formal-conjectures statements/oeis-a309717.lean (declaration OMA.S_oeis_a309717.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated identity holds, for every n).
-- Proof: S_t = x / D_t with D_t = 1 - t x - x^2. Partial fractions give
-- 2 S_1 S_2 S_3 = S_1 - 2 S_2 + S_3, since D_1 - D_2 = D_2 - D_3 = x; this is checked by multiplying
-- by D_1 D_2 D_3, which is not a zero divisor in Z[[x]].

namespace OMA.P_oeis_a309717

open OMA.S_oeis_a309717 PowerSeries

theorem hD (t : ℤ) : series t - C t * (X * series t) - X ^ 2 * series t = X := by
  ext n
  rcases n with _ | _ | n
  · simp [series, fibPoly, coeff_X_pow_mul']
  · rw [map_sub, map_sub, coeff_C_mul, coeff_succ_X_mul]
    simp [series, fibPoly, coeff_X_pow_mul', coeff_X]
  · rw [map_sub, map_sub, coeff_C_mul, coeff_succ_X_mul,
      show n + 1 + 1 = n + 2 from rfl, coeff_X_pow_mul]
    simp [series, fibPoly, coeff_X]

theorem key : 2 * (series 1 * series 2 * series 3) = series 1 - 2 * series 2 + series 3 := by
  have e1 := hD 1
  have e2 := hD 2
  have e3 := hD 3
  simp only [map_one, map_ofNat] at e1 e2 e3
  have h : ((1 - X - X ^ 2) * (1 - 2 * X - X ^ 2) * (1 - 3 * X - X ^ 2) : ℤ⟦X⟧) *
      (2 * (series 1 * series 2 * series 3) - (series 1 - 2 * series 2 + series 3)) = 0 := by
    linear_combination (2 * (1 - 2 * X - X ^ 2) * series 2 * (1 - 3 * X - X ^ 2) * series 3
        - (1 - 2 * X - X ^ 2) * (1 - 3 * X - X ^ 2)) * e1
      + (2 * X * (1 - 3 * X - X ^ 2) * series 3 + 2 * (1 - X - X ^ 2) * (1 - 3 * X - X ^ 2)) * e2
      + (2 * X ^ 2 - (1 - X - X ^ 2) * (1 - 2 * X - X ^ 2)) * e3
  have hne : ((1 - X - X ^ 2) * (1 - 2 * X - X ^ 2) * (1 - 3 * X - X ^ 2) : ℤ⟦X⟧) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hne)

theorem main' : ∀ n : ℕ, 3 ≤ n → 2 * a n = triangle n 3 := by
  intro n _
  have h := congrArg (coeff n) key
  unfold a
  rw [show (2 : ℤ) * coeff n (series 1 * series 2 * series 3)
      = coeff n (2 * (series 1 * series 2 * series 3)) from by
    rw [show (2 : ℤ⟦X⟧) = C (2 : ℤ) from by simp only [map_ofNat], coeff_C_mul]]
  rw [h]
  simp only [triangle, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [show (2 : ℤ⟦X⟧) = C (2 : ℤ) from by simp only [map_ofNat]]
  rw [map_add, map_sub, coeff_C_mul]
  simp [series]
  ring

end OMA.P_oeis_a309717

theorem OMA.solution : type_of% @OMA.S_oeis_a309717.main := OMA.P_oeis_a309717.main'
