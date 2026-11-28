import OMAStatements.S_mo_295497
import Mathlib

-- Problem: mo-295497, every lower semicontinuous real function on a closed subset A of a
-- metric space extends to a lower semicontinuous function on the whole space.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Put F = f on A and F(x) = 1 / dist(x, A) off A. Off A this is continuous. At a point x of A,
-- nearby points of A are handled by the lower semicontinuity of f, and nearby points x' off A
-- have dist(x', A) <= dist(x', x), so F(x') is as large as we like.

open Topology in
theorem OMA.solution : type_of% @OMA.S_mo_295497.main := by
  intro X _ A hA f hf
  classical
  rcases A.eq_empty_or_nonempty with hemp | hne
  · refine ⟨fun _ => 0, lowerSemicontinuous_const, ?_⟩
    rintro ⟨a, ha⟩
    have hfalse : a ∈ (∅ : Set X) := hemp ▸ ha
    exact False.elim hfalse
  have hposOff : ∀ z : X, z ∉ A → 0 < Metric.infDist z A := by
    intro z hz
    by_contra hnot
    have hzero : Metric.infDist z A = 0 :=
      le_antisymm (not_lt.mp hnot) Metric.infDist_nonneg
    have hmem : z ∈ closure A := (Metric.mem_closure_iff_infDist_zero hne).mpr hzero
    rw [hA.closure_eq] at hmem
    exact hz hmem
  refine ⟨fun x => if h : x ∈ A then f ⟨x, h⟩ else (Metric.infDist x A)⁻¹, ?_, ?_⟩
  · intro x y hy
    by_cases hx : x ∈ A
    · simp only [dif_pos hx] at hy
      have h1 := hf ⟨x, hx⟩ y hy
      rw [Metric.eventually_nhds_iff] at h1
      obtain ⟨ε, hε, h1⟩ := h1
      rw [Metric.eventually_nhds_iff]
      refine ⟨min ε (1 / (|y| + 1)), lt_min hε (by positivity), ?_⟩
      intro x' hx'
      by_cases hx'A : x' ∈ A
      · simp only [dif_pos hx'A]
        have hd : dist (⟨x', hx'A⟩ : A) ⟨x, hx⟩ < ε := lt_of_lt_of_le hx' (min_le_left _ _)
        exact h1 hd
      · simp only [dif_neg hx'A]
        have hpos := hposOff x' hx'A
        have hle : Metric.infDist x' A ≤ dist x' x := Metric.infDist_le_dist_of_mem hx
        have hlt : Metric.infDist x' A < 1 / (|y| + 1) :=
          lt_of_le_of_lt hle (lt_of_lt_of_le hx' (min_le_right _ _))
        have hypos : (0 : ℝ) < |y| + 1 := by positivity
        have h2 : |y| + 1 < (Metric.infDist x' A)⁻¹ := by
          rw [lt_inv_comm₀ hypos hpos]
          rw [one_div] at hlt
          exact hlt
        have h3 := le_abs_self y
        linarith
    · simp only [dif_neg hx] at hy
      have hpos := hposOff x hx
      have hcont : ContinuousAt (fun z => (Metric.infDist z A)⁻¹) x :=
        ((Metric.continuous_infDist_pt A).continuousAt).inv₀ hpos.ne'
      have hev1 : ∀ᶠ z in 𝓝 x, y < (Metric.infDist z A)⁻¹ :=
        hcont.eventually (lt_mem_nhds hy)
      have hev2 : ∀ᶠ z in 𝓝 x, z ∉ A := hA.isOpen_compl.mem_nhds hx
      filter_upwards [hev1, hev2] with z hz1 hz2
      simp only [dif_neg hz2]
      exact hz1
  · rintro ⟨a, ha⟩
    simp only [dif_pos ha]
