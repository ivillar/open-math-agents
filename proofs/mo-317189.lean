import OMAStatements.S_mo_317189
import Mathlib

-- Problem: mo-317189, is 2 |A + A| <= |A + A + A| + |A| for every finite set A of integers
-- containing a nonzero element?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For A = {0, 1, 3, 4}: A + A = {0, ..., 8} has 9 elements and A + A + A = {0, ..., 12} has
-- 13 elements, so 2 * 9 = 18 > 13 + 4 = 17.

open Pointwise

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_317189.main) := by
  intro h
  have key := h {0, 1, 3, 4} ⟨1, by decide, by decide⟩
  revert key
  decide +kernel
