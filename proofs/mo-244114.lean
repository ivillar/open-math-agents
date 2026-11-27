import OMAStatements.S_mo_244114
import Mathlib

-- Problem: mo-244114, is an ideal of K[x_1..x_n] radical as soon as all its restrictions to
-- lines parallel to the coordinate axes are radical?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For n = 2 take I = (x - y, x^2), a double point at the origin along the diagonal.
-- It is not radical (x^2 is in I but x is not), yet on the line y = a it restricts to
-- (x - a, x^2), which is (x) for a = 0 and the unit ideal otherwise, and on the line x = a it
-- restricts to (a - y, a^2), which is (y) for a = 0 and the unit ideal otherwise.

open Polynomial in
open OMA.S_mo_244114 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_244114.main) := by
  intro h
  have hXrad : (Ideal.span ({(X : ℂ[X])} : Set ℂ[X])).IsRadical :=
    ((Ideal.span_singleton_prime X_ne_zero).mpr prime_X).isRadical
  have hI := h ℂ 2 le_rfl
    (Ideal.span {MvPolynomial.X 0 - MvPolynomial.X 1, MvPolynomial.X 0 ^ 2}) ?_
  · have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ∈
        Ideal.span {MvPolynomial.X 0 - MvPolynomial.X 1, MvPolynomial.X 0 ^ 2} := by
      apply hI
      exact Ideal.mem_radical_iff.mpr ⟨2, Ideal.subset_span (by simp)⟩
    have hmap := Ideal.mem_map_of_mem
      (MvPolynomial.eval₂Hom (C : ℂ →+* ℂ[X]) (fun _ : Fin 2 => (X : ℂ[X]))) hmem
    rw [Ideal.map_span, Set.image_pair] at hmap
    simp only [map_sub, map_pow, MvPolynomial.eval₂Hom_X', sub_self] at hmap
    rw [Ideal.mem_span_pair] at hmap
    obtain ⟨p, q, hpq⟩ := hmap
    have hcoeff := congrArg (fun r : ℂ[X] => r.coeff 1) hpq
    simp [Polynomial.coeff_mul_X_pow'] at hcoeff
  · intro i a
    rw [Ideal.map_span, Set.image_pair]
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · have h0 : specialize (0 : Fin 2) a (MvPolynomial.X 0 - MvPolynomial.X 1) =
          X - C (a 1) := by
        simp [specialize]
      have h1 : specialize (0 : Fin 2) a (MvPolynomial.X 0 ^ 2) = X ^ 2 := by
        simp [specialize]
      rw [h0, h1]
      by_cases ha : a 1 = 0
      · have heq : Ideal.span ({X - C (a 1), X ^ 2} : Set ℂ[X]) = Ideal.span {X} := by
          apply le_antisymm
          · rw [Ideal.span_le]
            rintro x (rfl | rfl)
            · exact Ideal.mem_span_singleton.mpr ⟨1, by rw [ha]; simp⟩
            · exact Ideal.mem_span_singleton.mpr ⟨X, by ring⟩
          · rw [Ideal.span_le]
            rintro x rfl
            exact Ideal.mem_span_pair.mpr ⟨1, 0, by rw [ha]; simp⟩
        rw [heq]
        exact hXrad
      · have hmem : (C (a 1)) ^ 2 ∈ Ideal.span ({X - C (a 1), X ^ 2} : Set ℂ[X]) :=
          Ideal.mem_span_pair.mpr ⟨-(X + C (a 1)), 1, by ring⟩
        have hunit : IsUnit ((C (a 1) : ℂ[X]) ^ 2) :=
          (isUnit_C.mpr (IsUnit.mk0 _ ha)).pow 2
        rw [Ideal.eq_top_of_isUnit_mem _ hmem hunit]
        exact le_top
    · have h0 : specialize (1 : Fin 2) a (MvPolynomial.X 0 - MvPolynomial.X 1) =
          C (a 0) - X := by
        simp [specialize]
      have h1 : specialize (1 : Fin 2) a (MvPolynomial.X 0 ^ 2) = C (a 0) ^ 2 := by
        simp [specialize]
      rw [h0, h1]
      by_cases ha : a 0 = 0
      · have heq : Ideal.span ({C (a 0) - X, C (a 0) ^ 2} : Set ℂ[X]) = Ideal.span {X} := by
          apply le_antisymm
          · rw [Ideal.span_le]
            rintro x (rfl | rfl)
            · exact Ideal.mem_span_singleton.mpr ⟨-1, by rw [ha]; simp⟩
            · rw [ha]
              simp
          · rw [Ideal.span_le]
            rintro x rfl
            exact Ideal.mem_span_pair.mpr ⟨-1, 0, by rw [ha]; simp⟩
        rw [heq]
        exact hXrad
      · have hmem : (C (a 0)) ^ 2 ∈ Ideal.span ({C (a 0) - X, C (a 0) ^ 2} : Set ℂ[X]) :=
          Ideal.subset_span (by simp)
        have hunit : IsUnit ((C (a 0) : ℂ[X]) ^ 2) :=
          (isUnit_C.mpr (IsUnit.mk0 _ ha)).pow 2
        rw [Ideal.eq_top_of_isUnit_mem _ hmem hunit]
        exact le_top
