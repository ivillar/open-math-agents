import OMAStatements.S_mo_247291
import Mathlib

-- Problem: mo-247291, if U is unitary and conj(U) U is a diagonal matrix D with unimodular
-- entries, is D^2 = 1?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For U = [0 1; i 0] one gets conj(U) U = diag(i, -i), whose square is -1.

open Matrix in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_247291.main) := by
  intro h
  have hU : (!![0, 1; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  have hd : ∀ i : Fin 2, ‖(![Complex.I, -Complex.I] : Fin 2 → ℂ) i‖ = 1 := by
    intro i
    fin_cases i <;> simp
  have hprod : (!![0, 1; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ).map star *
      !![0, 1; Complex.I, 0] = diagonal ![Complex.I, -Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  have hsq := h 2 _ hU _ hd hprod
  have h00 := congrFun (congrFun hsq 0) 0
  have e : ((diagonal ![Complex.I, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) ^ 2) 0 0 = -1 := by
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  rw [e] at h00
  norm_num at h00
