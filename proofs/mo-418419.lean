import OMAStatements.S_mo_418419
import Mathlib

-- Problem: mo-418419, if R is integrally closed in a domain S, does every prime ideal of R
-- extend to a prime ideal of S?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. The integers are integrally closed in the rationals, but the prime ideal (2) extends to
-- the unit ideal of Q, which is not prime.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_418419.main) := by
  intro h
  have hinj : Function.Injective (algebraMap ℤ ℚ) := by
    intro a b hab
    exact_mod_cast hab
  have hic : IsIntegrallyClosedIn ℤ ℚ :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn ℚ).mp inferInstance
  have hP : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
  have hprime := h ℤ ℚ hinj hic (Ideal.span ({(2 : ℤ)} : Set ℤ)) hP
  have hmem : (algebraMap ℤ ℚ) 2 ∈ (Ideal.span ({(2 : ℤ)} : Set ℤ)).map (algebraMap ℤ ℚ) :=
    Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self 2)
  have hunit : IsUnit ((algebraMap ℤ ℚ) 2) := by
    rw [isUnit_iff_ne_zero]
    norm_num
  exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)
