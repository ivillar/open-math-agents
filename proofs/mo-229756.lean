import OMAStatements.S_mo_229756
import Mathlib

-- Problem: mo-229756, a measurable subgroup H of a locally compact abelian group with
-- 0 < mu(H) < infinity (mu a Haar measure) is open and compact.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- By the Steinhaus theorem H / H = H is a neighbourhood of 1, so H is an open subgroup. The
-- restriction of mu to H is then a left-invariant measure on the locally compact group H that
-- is positive on nonempty open sets. If H were not compact, such a measure would give infinite
-- mass to the whole group, contradicting mu(H) < infinity.

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped ENNReal Pointwise Topology

theorem OMA.solution : type_of% @OMA.S_mo_229756.main := by
  intro G _ _ _ _ _ _ _ μ _ _ H hH hpos hfin
  have hnhds : (H : Set G) ∈ 𝓝 (1 : G) := by
    have h := div_mem_nhds_one_of_haar_pos_ne_top μ (H : Set G) hH hpos hfin
    refine Filter.mem_of_superset h ?_
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact H.div_mem ha hb
  have hopen : IsOpen (H : Set G) := Subgroup.isOpen_of_mem_nhds H hnhds
  refine ⟨hopen, ?_⟩
  by_contra hnc
  have hncs : NoncompactSpace H := by
    rw [← not_compactSpace_iff]
    intro hc
    exact hnc ((isCompact_iff_compactSpace (s := (H : Set G))).mpr hc)
  have hlc : LocallyCompactSpace H := hopen.locallyCompactSpace
  obtain ⟨ν, hν⟩ : ∃ ν : Measure H, ν = μ.comap (Subtype.val : H → G) := ⟨_, rfl⟩
  have key : ∀ t : Set H, ν t = μ (Subtype.val '' t) := by
    intro t
    rw [hν]
    exact comap_subtype_coe_apply hH μ t
  have hop : IsOpenPosMeasure ν := by
    refine ⟨fun U hU hne => ?_⟩
    rw [key U]
    exact IsOpenPosMeasure.open_pos _ (hopen.isOpenMap_subtype_val U hU) (hne.image _)
  have hinv : ν.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (continuous_const_mul g).measurable hs, key, key]
    have e : Subtype.val '' ((fun x : H => g * x) ⁻¹' s) =
        (fun y : G => (g : G) * y) ⁻¹' (Subtype.val '' s) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        have hx : x ∈ H := by
          have h1 : (g : G)⁻¹ * (z : G) = x := by
            rw [hzx]
            exact inv_mul_cancel_left _ _
          rw [← h1]
          exact H.mul_mem (H.inv_mem g.2) z.2
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        have h2 : g * ⟨x, hx⟩ = z := Subtype.ext hzx.symm
        show g * ⟨x, hx⟩ ∈ s
        rw [h2]
        exact hz
    rw [e, measure_preimage_mul]
  have htop := measure_univ_of_isMulLeftInvariant ν
  rw [key, Subtype.coe_image_univ] at htop
  exact hfin htop
