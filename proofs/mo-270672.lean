import OMAStatements.S_mo_270672
import Mathlib

-- Problem: mo-270672, is every square matrix over F_p either orthogonal or completely
-- non-orthogonal?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Over F_2 the matrix A = diag(1, 0) is not orthogonal, and P = A is a nonzero symmetric
-- idempotent commuting with A with P A^T A = P A A^T = P.

open Matrix in
open OMA.S_mo_270672 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_270672.main) := by
  intro h
  rcases h 2 2 !![1, 0; 0, 0] with ho | hc
  · have h1 := ho.1
    revert h1
    decide
  · apply hc
    refine ⟨!![1, 0; 0, 0], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
