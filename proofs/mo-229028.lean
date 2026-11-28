import OMAStatements.S_mo_229028
import Mathlib

-- Problem: mo-229028, is a polynomial with nonnegative log-concave coefficients a log-concave
-- function on [0, infinity)?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take p = 1 + x + x^2, whose coefficient sequence 1, 1, 1 is log-concave. With x = 0,
-- y = 1/2 and t = 1/2 log-concavity of the function would give
-- sqrt (p(0) p(1/2)) = sqrt (7/4) <= p(1/4) = 21/16, but (21/16)^2 = 441/256 < 448/256 = 7/4.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_229028.main) := by
  intro h
  have hc : ∀ k, (∑ i ∈ Finset.range 3, (Polynomial.X : Polynomial ℝ) ^ i).coeff k =
      if k < 3 then 1 else 0 := by
    intro k
    simp [Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]
  have h1 := h (∑ i ∈ Finset.range 3, (Polynomial.X : Polynomial ℝ) ^ i)
    (by
      intro k
      rw [hc]
      split_ifs <;> norm_num)
    (by
      intro k _
      simp only [hc]
      split_ifs <;> first | omega | norm_num)
    0 (1 / 2) (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
  have e0 : (∑ i ∈ Finset.range 3, (Polynomial.X : Polynomial ℝ) ^ i).eval 0 = 1 := by
    simp [Polynomial.eval_finset_sum, Finset.sum_range_succ]
  have e1 : (∑ i ∈ Finset.range 3, (Polynomial.X : Polynomial ℝ) ^ i).eval (1 / 2) = 7 / 4 := by
    simp [Polynomial.eval_finset_sum, Finset.sum_range_succ]
    norm_num
  have e2 : (∑ i ∈ Finset.range 3, (Polynomial.X : Polynomial ℝ) ^ i).eval
      ((1 - 1 / 2) * 0 + 1 / 2 * (1 / 2)) = 21 / 16 := by
    simp [Polynomial.eval_finset_sum, Finset.sum_range_succ]
    norm_num
  rw [e0, e1, e2, Real.one_rpow, one_mul] at h1
  have h2 := mul_self_le_mul_self (Real.rpow_nonneg (by norm_num) _) h1
  have h3 : (7 / 4 : ℝ) ^ (1 / 2 : ℝ) * (7 / 4 : ℝ) ^ (1 / 2 : ℝ) = 7 / 4 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  rw [h3] at h2
  norm_num at h2
