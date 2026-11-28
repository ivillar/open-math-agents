import OMAStatements.S_mo_300152
import Mathlib

-- Problem: mo-300152, is sum_{i=1}^m C(m,i) (-1)^(i-1) r_i^2 at most
-- sum_{i=1}^m C(m,i) (-1)^(i-1) r_i for 1 >= r_1 >= ... >= r_m >= 0?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For m = 2 and r = (1, 1/2) the left side is 2 - 1/4 = 7/4 and the right side is
-- 2 - 1/2 = 3/2.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_300152.main) := by
  intro h
  have h2 := h 2 (fun i => if i ≤ 1 then 1 else 1 / 2) ?_ ?_
  · have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
    rw [hI, Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num)] at h2
    norm_num [Nat.choose] at h2
  · intro i
    show 0 ≤ (if i ≤ 1 then (1 : ℝ) else 1 / 2) ∧ (if i ≤ 1 then (1 : ℝ) else 1 / 2) ≤ 1
    split_ifs <;> norm_num
  · intro a b hab
    show (if b ≤ 1 then (1 : ℝ) else 1 / 2) ≤ (if a ≤ 1 then (1 : ℝ) else 1 / 2)
    by_cases ha : a ≤ 1
    · rw [if_pos ha]
      split_ifs <;> norm_num
    · have hb : ¬ b ≤ 1 := by omega
      rw [if_neg ha, if_neg hb]
