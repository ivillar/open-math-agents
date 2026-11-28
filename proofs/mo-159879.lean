import OMAStatements.S_mo_159879
import Mathlib

-- Problem: mo-159879, signs of the Fourier coefficients of the quadratic form x^T B x on the
-- hypercube for a positive semidefinite B.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- The coefficients are not always nonzero (for the empty matrix the coefficient is 0), and
-- not always nonnegative: for B = [1 -1; -1 1] = v v^T with v = (1, -1) and S = {0, 1} the
-- coefficient is 2 B_01 = -2.

open Matrix in
open OMA.S_mo_159879 in
theorem OMA.solution : type_of% @OMA.S_mo_159879.main := by
  constructor
  · intro h
    have h0 := h 0 (0 : Matrix (Fin 0) (Fin 0) ℝ) Matrix.PosSemidef.zero ∅
    apply h0
    simp [coefficient]
  · intro h
    have hpsd : (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
      have e : (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ) =
          (!![1, -1] : Matrix (Fin 1) (Fin 2) ℝ)ᴴ * (!![1, -1] : Matrix (Fin 1) (Fin 2) ℝ) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_one]
      rw [e]
      exact Matrix.posSemidef_conjTranspose_mul_self _
    have hneg := h 2 _ hpsd {0, 1}
    have hsum : ∀ F : (Fin 2 → Bool) → ℝ, ∑ b, F b =
        F ![true, true] + F ![true, false] + F ![false, true] + F ![false, false] := by
      intro F
      rw [← Equiv.sum_comp
        (⟨fun p => ![p.1, p.2], fun x => (x 0, x 1),
          fun p => by rcases p with ⟨a, b⟩; rfl,
          fun x => by ext i; fin_cases i <;> rfl⟩ : (Bool × Bool) ≃ (Fin 2 → Bool)) F]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, Equiv.coe_fn_mk]
      ring
    have hval : coefficient (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ) {0, 1} = -2 := by
      unfold coefficient
      rw [hsum]
      norm_num [signVector, sign, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Finset.prod_pair (show (0 : Fin 2) ≠ 1 by decide)]
    rw [hval] at hneg
    norm_num at hneg
