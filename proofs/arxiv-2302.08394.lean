import OMAStatements.S_arxiv_2302_08394
import Mathlib

-- Problem: arxiv-2302.08394, the polynomial invariant A of rooted trees is not complete: two
-- non-isomorphic rooted trees on nine vertices have the same A (Burghart, arXiv:2302.08394,
-- Figure 1 and Remark 16).
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- The two trees are those of the source; the verification and the Lean proof are our own.

/-!
The trees `T1` and `T2` of Figure 1 and Remark 16 of arXiv:2302.08394, on nine vertices: `T1`
has parent map `0,0,0,1,1,2,4,6,6` and `T2` has parent map `0,0,0,1,2,2,3,3,7`. Their admissible
subtrees have the same multiset of (number of vertices, number of boundary vertices), so the
polynomials `A` agree. They are not isomorphic: walks of length three from the root end in three
vertices of `T1` and in four vertices of `T2`.
-/

namespace F2Tree

open OMA.S_arxiv_2302_08394

def T1 : RootedTree 8 := ⟨![0, 0, 0, 1, 1, 2, 4, 6, 6], by decide⟩

def T2 : RootedTree 8 := ⟨![0, 0, 0, 1, 2, 2, 3, 3, 7], by decide⟩

theorem hW1 : (Finset.univ.filter
    (fun v => ∃ a b, T1.Adj 0 a ∧ T1.Adj a b ∧ T1.Adj b v)).card = 3 := by decide +kernel

theorem hW2 : (Finset.univ.filter
    (fun v => ∃ a b, T2.Adj 0 a ∧ T2.Adj a b ∧ T2.Adj b v)).card = 4 := by decide +kernel

theorem key : (Finset.univ.filter T1.IsAdmissible).val.map (fun S => (S.card, T1.boundaryCard S)) =
    (Finset.univ.filter T2.IsAdmissible).val.map (fun S => (S.card, T2.boundaryCard S)) := by
  decide +kernel

theorem A_eq {n : ℕ} (T : RootedTree n) : T.A =
    (((Finset.univ.filter T.IsAdmissible).val.map (fun S => (S.card, T.boundaryCard S))).map
      (fun p : ℕ × ℕ =>
        (MvPolynomial.X 0 ^ p.1 * MvPolynomial.X 1 ^ p.2 : MvPolynomial (Fin 2) ℤ))).sum := by
  rw [Multiset.map_map]
  rfl

theorem not_iso : ¬ T1.Isomorphic T2 := by
  rintro ⟨σ, h0, hadj⟩
  have hcard : (Finset.univ.filter
      (fun v => ∃ a b, T1.Adj 0 a ∧ T1.Adj a b ∧ T1.Adj b v)).card =
      (Finset.univ.filter (fun v => ∃ a b, T2.Adj 0 a ∧ T2.Adj a b ∧ T2.Adj b v)).card := by
    apply Finset.card_bij (fun v _ => σ v)
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      obtain ⟨_, a, b, h1, h2, h3⟩ := hv
      refine ⟨Finset.mem_univ _, σ a, σ b, ?_, (hadj a b).mp h2, (hadj b v).mp h3⟩
      have h4 := (hadj 0 a).mp h1
      rw [h0] at h4
      exact h4
    · intro v _ w _ h
      exact σ.injective h
    · intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨_, a, b, h1, h2, h3⟩ := hu
      refine ⟨σ.symm u, ?_, σ.apply_symm_apply u⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, σ.symm a, σ.symm b, ?_, ?_, ?_⟩
      · rw [hadj, h0, σ.apply_symm_apply]
        exact h1
      · rw [hadj, σ.apply_symm_apply, σ.apply_symm_apply]
        exact h2
      · rw [hadj, σ.apply_symm_apply, σ.apply_symm_apply]
        exact h3
  rw [hW1, hW2] at hcard
  omega

theorem not_complete : ∃ (n : ℕ) (T₁ T₂ : RootedTree n), ¬ T₁.Isomorphic T₂ ∧ T₁.A = T₂.A :=
  ⟨8, T1, T2, not_iso, by rw [A_eq T1, A_eq T2, key]⟩

end F2Tree

theorem OMA.solution : type_of% @OMA.S_arxiv_2302_08394.main := F2Tree.not_complete
