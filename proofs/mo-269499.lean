import OMAStatements.S_mo_269499
import Mathlib

-- Problem: mo-269499, a claimed inequality between diagonal entries of X^T D1 P D2 P^T D3 X
-- and X^T D1 D2 D3 X, where P is the projection onto the column space of X.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Counterexample: X = [1 2; 1 1; 1 1], so P = [1 0 0; 0 1/2 1/2; 0 1/2 1/2] = X Y with
-- Y = [-1 1 1; 1 -1/2 -1/2]. With D1 = D3 = diag(1, 1, 2) and D2 = I the [1,1] entries are
-- 11/2 on the projected side and 6 on the other side.

open Matrix in
open OMA.S_mo_269499 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_269499.main) := by
  intro h
  have hx : ∀ i : Fin 3, 0 < (![2, 1, 1] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i <;> simp
  have hd1 : ∀ i : Fin 3, 0 < (![1, 1, 2] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i <;> simp
  have hd2 : ∀ i : Fin 3, 0 < (![1, 1, 1] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i <;> simp
  have hPt : (!![1, 0, 0; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ =
      !![1, 0, 0; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hPP : (!![1, 0, 0; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2] : Matrix (Fin 3) (Fin 3) ℝ) *
      !![1, 0, 0; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2] =
      !![1, 0, 0; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  have hPX : (!![1, 0, 0; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2] : Matrix (Fin 3) (Fin 3) ℝ) *
      designMatrix ![2, 1, 1] = designMatrix ![2, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [designMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  have hXY : (!![1, 0, 0; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2] : Matrix (Fin 3) (Fin 3) ℝ) =
      designMatrix ![2, 1, 1] *
        (!![-1, 1, 1; 1, -1 / 2, -1 / 2] : Matrix (Fin 2) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [designMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hmain := h 3 ![2, 1, 1] hx _ hPt hPP hPX ⟨_, hXY⟩ ![1, 1, 2] ![1, 1, 1] ![1, 1, 2]
    hd1 hd2 hd1 0
  simp [designMatrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] at hmain
  norm_num at hmain
