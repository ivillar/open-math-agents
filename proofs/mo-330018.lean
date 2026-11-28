import OMAStatements.S_mo_330018
import Mathlib

-- Problem: mo-330018, continuous maps from a Fort space (open sets are the sets missing b and
-- the cofinite sets) to [0, 1].
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- The range is bounded because it lies in [0, 1]. If f is continuous, the preimage of the open
-- ball of radius e around f(b) is an open set containing b, hence cofinite. Conversely, if
-- f(x) is e-far from f(b) only for finitely many x, then the preimage of an open set V either
-- misses b or contains the preimage of a ball around f(b), which is cofinite.

open OMA.S_mo_330018 in
theorem OMA.solution : type_of% @OMA.S_mo_330018.main := by
  intro X _ _ b hFort f
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · refine (Metric.isBounded_Icc (0 : ℝ) 1).subset ?_
    rintro _ ⟨x, rfl⟩
    exact (f x).2
  · intro hf ε hε
    have hopen : IsOpen (f ⁻¹' Metric.ball (f b) ε) := Metric.isOpen_ball.preimage hf
    have hb : b ∈ f ⁻¹' Metric.ball (f b) ε := Metric.mem_ball_self hε
    rcases (hFort _).mp hopen with h1 | h1
    · exact absurd hb h1
    · refine h1.subset ?_
      intro x hx hmem
      have hx' : ε ≤ dist (f x) (f b) := hx
      have hlt : dist (f x) (f b) < ε := hmem
      linarith
  · intro hfin
    rw [continuous_def]
    intro V hV
    rw [hFort]
    by_cases hb : f b ∈ V
    · right
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV (f b) hb
      refine (hfin ε hε).subset ?_
      intro x hx
      show ε ≤ dist (f x) (f b)
      by_contra hlt
      exact hx (hball (Metric.mem_ball.mpr (not_le.mp hlt)))
    · left
      exact hb
