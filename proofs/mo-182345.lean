import OMAStatements.S_mo_182345
import Mathlib

-- Problem: mo-182345, for a positive one-parameter semigroup Z on a Banach lattice and f >= 0,
-- is the integral over [0,1] of Z(1-s) f + Z(1+s) f at least f?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Not as stated (no continuity in t is assumed). On X = R let Z(0) = id and Z(t) = 0 for
-- t > 0. This is a positive semigroup, the integrand vanishes on (0,1), so the integral is 0,
-- and for f = 1 the claimed inequality reads 0 <= -1.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_182345.main) := by
  intro h
  let Z : ℝ → (ℝ →L[ℝ] ℝ) := fun t => if t = 0 then ContinuousLinearMap.id ℝ ℝ else 0
  have hZ0 : Z 0 = ContinuousLinearMap.id ℝ ℝ := by simp [Z]
  have hZadd : ∀ t u : ℝ, 0 ≤ t → 0 ≤ u → Z (t + u) = (Z t).comp (Z u) := by
    intro t u ht hu
    by_cases h0 : t = 0
    · subst h0
      by_cases hu0 : u = 0
      · subst hu0
        simp [Z]
      · simp [Z, hu0]
    · have hne : t + u ≠ 0 := by
        intro hc
        apply h0
        linarith
      simp [Z, h0, hne]
  have hZpos : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝ, 0 ≤ x → 0 ≤ Z t x := by
    intro t _ x hx
    by_cases h0 : t = 0
    · simp [Z, h0, hx]
    · simp [Z, h0]
  have hfun : ∀ s ∈ Set.Ioo (0 : ℝ) 1, Z (1 - s) 1 + Z (1 + s) 1 = 0 := by
    intro s hs
    have h1 : (1 - s) ≠ 0 := by
      intro hc
      have := hs.2
      linarith
    have h2 : (1 + s) ≠ 0 := by
      intro hc
      have := hs.1
      linarith
    simp [Z, h1, h2]
  have hint : IntervalIntegrable (fun s : ℝ => Z (1 - s) 1 + Z (1 + s) 1)
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact (MeasureTheory.integrableOn_zero).congr_fun (fun s hs => (hfun s hs).symm)
      measurableSet_Ioo
  have hnorm : ∀ x y : ℝ, |x| ≤ |y| → ‖x‖ ≤ ‖y‖ := by
    intro x y hxy
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact hxy
  have hmain := h ℝ hnorm Z hZ0 hZadd hZpos 1 zero_le_one hint
  have hval : (∫ s in (0 : ℝ)..1, Z (1 - s) 1 + Z (1 + s) 1) = 0 := by
    rw [intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.setIntegral_congr_fun (g := fun _ => (0 : ℝ)) measurableSet_Ioo hfun]
    simp
  rw [hval] at hmain
  norm_num at hmain
