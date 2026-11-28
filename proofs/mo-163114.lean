import OMAStatements.S_mo_163114
import Mathlib

-- Problem: mo-163114, does the relation x <= y iff x * y = 0 of a BCL algebra define a partial
-- order?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No, transitivity can fail. On {0, 1, 2} with z = 0 take the operation with table
--   0*0 = 0, 0*1 = 0, 0*2 = 1; 1*0 = 1, 1*1 = 0, 1*2 = 0; 2*0 = 1, 2*1 = 2, 2*2 = 0.
-- The three BCL axioms hold (finite check), and 0 * 1 = 0, 1 * 2 = 0, but 0 * 2 = 1.

open OMA.S_mo_163114 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_163114.main) := by
  intro h
  have hB : IsBCL (fun x y : Fin 3 =>
      (![![0, 0, 1], ![1, 0, 0], ![1, 2, 0]] : Fin 3 → Fin 3 → Fin 3) x y) 0 := by
    unfold IsBCL
    decide
  have h3 := (h (Fin 3) _ 0 hB).2.2 0 1 2 (by decide) (by decide)
  revert h3
  decide
