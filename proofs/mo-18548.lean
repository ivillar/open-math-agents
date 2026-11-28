import OMAStatements.S_mo_18548
import Mathlib

-- Problem: mo-18548, a simplicial complex on three vertices whose face poset is not a lattice
-- and whose face poset with a top element added is not a distributive lattice.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Take the three isolated vertices: F = sets with at most one element. The faces {0} and {1}
-- have no common upper bound in F, so F is not a lattice. With a top element added the poset
-- is the diamond M_3 (bottom, three atoms, top): for the atoms a, b, c one has b v c = top and
-- a ^ b, a ^ c <= bottom, so distributivity would give a <= bottom.

open OMA.S_mo_18548 in
theorem OMA.solution : type_of% @OMA.S_mo_18548.main := by
  refine ⟨{s : Finset (Fin 3) | s.card ≤ 1}, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · show (∅ : Finset (Fin 3)).card ≤ 1
    simp
  · intro s t ht hst
    exact le_trans (Finset.card_le_card hst) ht
  · intro i
    show ({i} : Finset (Fin 3)).card ≤ 1
    simp
  · rintro ⟨L, hL⟩
    have ha : ({0} : Finset (Fin 3)) ∈ {s : Finset (Fin 3) | s.card ≤ 1} := by
      show ({0} : Finset (Fin 3)).card ≤ 1
      simp
    have hb : ({1} : Finset (Fin 3)) ∈ {s : Finset (Fin 3) | s.card ≤ 1} := by
      show ({1} : Finset (Fin 3)).card ≤ 1
      simp
    have h1 := (hL ⟨{0}, ha⟩ (⟨{0}, ha⟩ ⊔ ⟨{1}, hb⟩)).mp le_sup_left
    have h2 := (hL ⟨{1}, hb⟩ (⟨{0}, ha⟩ ⊔ ⟨{1}, hb⟩)).mp le_sup_right
    have hc : (⟨{0}, ha⟩ ⊔ ⟨{1}, hb⟩ : {s : Finset (Fin 3) | s.card ≤ 1}).val.card ≤ 1 :=
      (⟨{0}, ha⟩ ⊔ ⟨{1}, hb⟩ : {s : Finset (Fin 3) | s.card ≤ 1}).property
    have h01 := Finset.card_le_one.mp hc 0 (h1 (Finset.mem_singleton_self 0)) 1
      (h2 (Finset.mem_singleton_self 1))
    exact absurd h01 (by decide)
  · rintro ⟨L, hL⟩
    have ha : ({0} : Finset (Fin 3)) ∈ {s : Finset (Fin 3) | s.card ≤ 1} := by
      show ({0} : Finset (Fin 3)).card ≤ 1
      simp
    have hb : ({1} : Finset (Fin 3)) ∈ {s : Finset (Fin 3) | s.card ≤ 1} := by
      show ({1} : Finset (Fin 3)).card ≤ 1
      simp
    have hc : ({2} : Finset (Fin 3)) ∈ {s : Finset (Fin 3) | s.card ≤ 1} := by
      show ({2} : Finset (Fin 3)).card ≤ 1
      simp
    have h0 : (∅ : Finset (Fin 3)) ∈ {s : Finset (Fin 3) | s.card ≤ 1} := by
      show (∅ : Finset (Fin 3)).card ≤ 1
      simp
    have hmeet : ∀ (i j : Fin 3) (hi : ({i} : Finset (Fin 3)) ∈ {s : Finset (Fin 3) | s.card ≤ 1})
        (hj : ({j} : Finset (Fin 3)) ∈ {s : Finset (Fin 3) | s.card ≤ 1}), i ≠ j →
        @LE.le _ L.toLE
          (some ⟨{i}, hi⟩ ⊓ some ⟨{j}, hj⟩ : Option {s : Finset (Fin 3) | s.card ≤ 1})
          (some ⟨∅, h0⟩) := by
      intro i j hi hj hij
      have g1 := (hL (some ⟨{i}, hi⟩ ⊓ some ⟨{j}, hj⟩) (some ⟨{i}, hi⟩)).mp inf_le_left
      have g2 := (hL (some ⟨{i}, hi⟩ ⊓ some ⟨{j}, hj⟩) (some ⟨{j}, hj⟩)).mp inf_le_right
      rw [hL]
      rcases hinf : (some ⟨{i}, hi⟩ ⊓ some ⟨{j}, hj⟩ :
          Option {s : Finset (Fin 3) | s.card ≤ 1}) with _ | s
      · rw [hinf] at g1
        exact False.elim g1
      · rw [hinf] at g1 g2
        show s.val ⊆ ∅
        intro x hx
        have e1 : x = i := Finset.mem_singleton.mp (g1 hx)
        have e2 : x = j := Finset.mem_singleton.mp (g2 hx)
        exact absurd (e1.symm.trans e2) hij
    have hjoin : (some ⟨{1}, hb⟩ ⊔ some ⟨{2}, hc⟩ :
        Option {s : Finset (Fin 3) | s.card ≤ 1}) = none := by
      have g1 := (hL (some ⟨{1}, hb⟩) (some ⟨{1}, hb⟩ ⊔ some ⟨{2}, hc⟩)).mp le_sup_left
      have g2 := (hL (some ⟨{2}, hc⟩) (some ⟨{1}, hb⟩ ⊔ some ⟨{2}, hc⟩)).mp le_sup_right
      rcases hsup : (some ⟨{1}, hb⟩ ⊔ some ⟨{2}, hc⟩ :
          Option {s : Finset (Fin 3) | s.card ≤ 1}) with _ | t
      · rfl
      · rw [hsup] at g1 g2
        have g1' : ({1} : Finset (Fin 3)) ⊆ t.val := g1
        have g2' : ({2} : Finset (Fin 3)) ⊆ t.val := g2
        have h12 := Finset.card_le_one.mp t.property 1 (g1' (Finset.mem_singleton_self 1)) 2
          (g2' (Finset.mem_singleton_self 2))
        exact absurd h12 (by decide)
    have hale : @LE.le _ L.toLE (some ⟨{0}, ha⟩ : Option {s : Finset (Fin 3) | s.card ≤ 1})
        (some ⟨{1}, hb⟩ ⊔ some ⟨{2}, hc⟩) := by
      rw [hjoin, hL]
      trivial
    have hdist : @LE.le _ L.toLE (some ⟨{0}, ha⟩ : Option {s : Finset (Fin 3) | s.card ≤ 1})
        (some ⟨{0}, ha⟩ ⊓ some ⟨{1}, hb⟩ ⊔ some ⟨{0}, ha⟩ ⊓ some ⟨{2}, hc⟩) := by
      rw [← inf_sup_left]
      exact le_inf le_rfl hale
    have hfinal := le_trans hdist
      (sup_le (hmeet 0 1 ha hb (by decide)) (hmeet 0 2 ha hc (by decide)))
    have hsub : ({0} : Finset (Fin 3)) ⊆ ∅ := (hL _ _).mp hfinal
    exact absurd (hsub (Finset.mem_singleton_self 0)) (Finset.notMem_empty 0)
