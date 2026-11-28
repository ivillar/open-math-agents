import OMAStatements.S_mo_258600
import Mathlib

-- Problem: mo-258600, does a surjective ring homomorphism A -> B induce a surjection
-- GL_n(A) -> GL_n(B) for n > 1?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For Z -> Z/5 and n = 2 the matrix diag(2, 1) is invertible over Z/5 with determinant 2,
-- but every invertible integer matrix has determinant 1 or -1, which map to 1 and 4.

open Matrix in
open OMA.S_mo_258600 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_258600.main) := by
  intro h
  have hsurj : Function.Surjective (Int.castRingHom (ZMod 5)) := by
    intro x
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective x
    exact ⟨k, hk⟩
  have hs := h ℤ (ZMod 5) (Int.castRingHom (ZMod 5)) hsurj 2 (by norm_num)
  obtain ⟨M, hM⟩ := hs ⟨!![2, 0; 0, 1], !![3, 0; 0, 1], by decide, by decide⟩
  have hval : (M : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod 5)) =
      (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 5)) := congrArg Units.val hM
  have hdet : (Int.castRingHom (ZMod 5)) (M : Matrix (Fin 2) (Fin 2) ℤ).det = 2 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hval, Matrix.det_fin_two]
    decide
  have hunit : IsUnit (M : Matrix (Fin 2) (Fin 2) ℤ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp M.isUnit
  rcases Int.isUnit_iff.mp hunit with h1 | h1
  · rw [h1, map_one] at hdet
    exact absurd hdet (by decide)
  · rw [h1, map_neg, map_one] at hdet
    exact absurd hdet (by decide)
