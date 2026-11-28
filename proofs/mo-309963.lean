import OMAStatements.S_mo_309963
import Mathlib

-- Problem: mo-309963, for a finite extension E/F and an E-linear operator T on a finite
-- dimensional E-vector space, det_F(T) = N_{E/F}(det_E(T)).
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- This is the transitivity of determinants along a tower, which is in Mathlib as
-- LinearMap.det_restrictScalars.

theorem OMA.solution : type_of% @OMA.S_mo_309963.main := by
  intro F E V _ _ _ _ _ _ _ _ _ _ T
  exact LinearMap.det_restrictScalars
