import OMAStatements.S_mo_185536
import Mathlib

-- Problem: mo-185536, the exponential map is injective on the self-adjoint elements of a
-- C*-algebra.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- For self-adjoint a the continuous functional calculus gives log (exp a) = a
-- (CFC.log_exp in Mathlib), so exp a = exp b forces a = b.

theorem OMA.solution : type_of% @OMA.S_mo_185536.main := by
  intro A _ a b ha hb hne h
  apply hne
  calc a = CFC.log (NormedSpace.exp a) := (CFC.log_exp a ha).symm
    _ = CFC.log (NormedSpace.exp b) := by rw [h]
    _ = b := CFC.log_exp b hb
