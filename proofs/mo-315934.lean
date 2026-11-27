import OMAStatements.S_mo_315934
import Mathlib

-- Problem: mo-315934, is the functor sending a group to its set of elements of finite order
-- representable?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. If A represented it, the universal element u of A (corresponding to the identity of A)
-- would have some finite order dividing N > 0, and every element of finite order of every
-- group would be the image of u, hence killed by N. A generator of Z/2N is not.

open CategoryTheory in
open OMA.S_mo_315934 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_315934.main) := by
  rintro ⟨A, ⟨R⟩⟩
  have hu : IsOfFinOrder (R.equiv A (𝟙 A)).val := (R.equiv A (𝟙 A)).property
  obtain ⟨N, hNpos, hN⟩ := isOfFinOrder_iff_pow_eq_one.mp hu
  have hN2 : NeZero (2 * N) := ⟨by omega⟩
  have hg : IsOfFinOrder (Multiplicative.ofAdd (1 : ZMod (2 * N))) := isOfFinOrder_of_finite _
  obtain ⟨f, hf⟩ := (R.equiv (GrpCat.of (Multiplicative (ZMod (2 * N))))).surjective
    ⟨Multiplicative.ofAdd (1 : ZMod (2 * N)), hg⟩
  have hc := R.compatible A (GrpCat.of (Multiplicative (ZMod (2 * N)))) (𝟙 A) f
  rw [Category.id_comp, hf] at hc
  have h1 : Multiplicative.ofAdd (1 : ZMod (2 * N)) = f.hom (R.equiv A (𝟙 A)).val := hc
  have hpow : (Multiplicative.ofAdd (1 : ZMod (2 * N))) ^ N = 1 := by
    rw [h1, ← map_pow, hN, map_one]
  have h2 : ((N : ℕ) : ZMod (2 * N)) = 0 := by
    have h3 := congrArg Multiplicative.toAdd hpow
    simpa using h3
  have h4 : 2 * N ∣ N := (ZMod.natCast_eq_zero_iff N (2 * N)).mp h2
  have h5 := Nat.le_of_dvd hNpos h4
  omega
