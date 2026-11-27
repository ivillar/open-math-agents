import OMAStatements.S_mo_369944
import Mathlib

-- Problem: mo-369944, a positive continuous functional on a subspace of C(K) with no positive
-- linear extension to C(K).
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- On K = [0,1] let M be spanned by x and x^2 and let L(f) = 4 f(1/2) - f(1), so that
-- L(a x + b x^2) = a. If a x + b x^2 >= 0 on [0,1] then a >= 0, so L is positive on M. A
-- positive extension E would satisfy E(x) = 1 and E(x^2) = 0, but with c = E(1) >= 0 the
-- function ((c+1) x - 1)^2 >= 0 is sent to -c - 2 < 0.

theorem OMA.solution : type_of% @OMA.S_mo_369944.main := by
  let f1 : C(Set.Icc (0 : ℝ) 1, ℝ) := ⟨fun x => x.1, continuous_subtype_val⟩
  let f2 : C(Set.Icc (0 : ℝ) 1, ℝ) := ⟨fun x => x.1 ^ 2, continuous_subtype_val.pow 2⟩
  let p1 : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  let ph : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  let Λ : C(Set.Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ :=
    (4 : ℝ) • ContinuousMap.evalCLM ℝ ph - ContinuousMap.evalCLM ℝ p1
  have hΛ : ∀ g : C(Set.Icc (0 : ℝ) 1, ℝ), Λ g = 4 * g ph - g p1 := by
    intro g
    simp [Λ]
  have hf1 : ∀ x : Set.Icc (0 : ℝ) 1, f1 x = x.1 := fun x => rfl
  have hf2 : ∀ x : Set.Icc (0 : ℝ) 1, f2 x = x.1 ^ 2 := fun x => rfl
  have hp1 : (p1 : ℝ) = 1 := rfl
  have hph : (ph : ℝ) = 1 / 2 := rfl
  refine ⟨Set.Icc (0 : ℝ) 1, inferInstance, inferInstance, Submodule.span ℝ {f1, f2},
    Λ.comp (Submodule.subtypeL _), ?_, ?_⟩
  · rintro ⟨f, hf⟩ hpos
    have hpos' : ∀ x, 0 ≤ f x := hpos
    show 0 ≤ Λ f
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hf
    have hval : ∀ x : Set.Icc (0 : ℝ) 1, (a • f1 + b • f2) x = a * x.1 + b * x.1 ^ 2 := by
      intro x
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul, hf1, hf2]
    rw [hΛ, hval, hval, hp1, hph]
    have hgoal : 4 * (a * (1 / 2) + b * (1 / 2) ^ 2) - (a * 1 + b * 1 ^ 2) = a := by ring
    rw [hgoal]
    by_contra hneg
    have ha : a < 0 := not_le.mp hneg
    have hone := hpos' p1
    rw [hval, hp1] at hone
    have hb : 0 < b := by linarith
    have ht0 : 0 < -a / (2 * b) := div_pos (by linarith) (by linarith)
    have ht1 : -a / (2 * b) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hx := hpos' ⟨-a / (2 * b), ⟨ht0.le, ht1⟩⟩
    rw [hval] at hx
    have hbne : b ≠ 0 := hb.ne'
    have hcomp : a * (-a / (2 * b)) + b * (-a / (2 * b)) ^ 2 = -(a ^ 2) / (4 * b) := by
      field_simp
      ring
    have hx' : 0 ≤ -(a ^ 2) / (4 * b) := by
      rw [← hcomp]
      exact hx
    have hlt : -(a ^ 2) / (4 * b) < 0 := div_neg_of_neg_of_pos (by nlinarith) (by linarith)
    linarith
  · rintro ⟨E, hE, hext⟩
    have hf1M : f1 ∈ Submodule.span ℝ {f1, f2} := Submodule.subset_span (by simp)
    have hf2M : f2 ∈ Submodule.span ℝ {f1, f2} := Submodule.subset_span (by simp)
    have e1 : E f1 = 1 := by
      have h1 := hext ⟨f1, hf1M⟩
      have h2 : E f1 = Λ f1 := h1
      rw [h2, hΛ, hf1, hf1, hp1, hph]
      norm_num
    have e2 : E f2 = 0 := by
      have h1 := hext ⟨f2, hf2M⟩
      have h2 : E f2 = Λ f2 := h1
      rw [h2, hΛ, hf2, hf2, hp1, hph]
      norm_num
    have hone : 0 ≤ E 1 := hE 1 (fun x => by simp)
    have hh := hE ((E 1 + 1) ^ 2 • f2 - (2 * (E 1 + 1)) • f1 + 1) (fun x => by
      simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, smul_eq_mul, hf1, hf2]
      nlinarith [sq_nonneg ((E 1 + 1) * x.1 - 1)])
    have hEh : E ((E 1 + 1) ^ 2 • f2 - (2 * (E 1 + 1)) • f1 + 1) = -(E 1) - 2 := by
      simp only [map_add, map_sub, map_smul, smul_eq_mul, e1, e2]
      ring
    rw [hEh] at hh
    linarith
