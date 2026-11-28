import OMAStatements.S_mo_138509
import Mathlib

-- Problem: mo-138509, if every nonempty vertex set W of a finite graph has a vertex with an
-- odd number of neighbours in W, then the number of vertices is even.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Let A be the adjacency matrix over Z/2. In the Leibniz expansion of det A the terms of a
-- permutation and of its inverse are equal (A is symmetric), so they cancel in pairs, and an
-- involution on an odd number of points has a fixed point i, contributing the factor
-- A i i = 0. Hence det A = 0 when the number of vertices is odd, so A w = 0 for some w != 0.
-- For W the support of w, every vertex then has an even number of neighbours in W.

open Matrix in
theorem OMA.solution : type_of% @OMA.S_mo_138509.main := by
  intro V _ G h
  classical
  by_contra hodd
  have hcard : Odd (Fintype.card V) := Nat.not_even_iff_odd.mp hodd
  obtain ⟨A, hA⟩ : ∃ A : Matrix V V (ZMod 2), ∀ a b, A a b = if G.Adj a b then 1 else 0 :=
    ⟨fun a b => if G.Adj a b then 1 else 0, fun a b => rfl⟩
  have hsymm : ∀ a b, A a b = A b a := by
    intro a b
    rw [hA, hA]
    by_cases hab : G.Adj a b
    · rw [if_pos hab, if_pos hab.symm]
    · rw [if_neg hab, if_neg (fun h' => hab h'.symm)]
  have hdiag : ∀ a, A a a = 0 := by
    intro a
    rw [hA, if_neg (G.irrefl)]
  have hdet : A.det = 0 := by
    rw [Matrix.det_apply]
    refine Finset.sum_involution (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
    · intro σ _
      have hprod : ∏ i, A (σ⁻¹ i) i = ∏ i, A (σ i) i := by
        rw [← Equiv.prod_comp σ (fun i => A (σ⁻¹ i) i)]
        apply Finset.prod_congr rfl
        intro i _
        have e : σ⁻¹ (σ i) = i := σ.symm_apply_apply i
        rw [e]
        exact hsymm i (σ i)
      rw [Equiv.Perm.sign_inv, hprod]
      exact CharTwo.add_self_eq_zero _
    · intro σ _ hne hinv
      apply hne
      have hσ2 : σ ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 1 [← hinv]
        exact inv_mul_cancel σ
      have h2 := Equiv.Perm.two_dvd_card_support hσ2
      have hex : ∃ i, i ∉ σ.support := by
        by_contra hall
        have hall' : ∀ i, i ∈ σ.support := by
          intro i
          by_contra hi
          exact hall ⟨i, hi⟩
        have huniv : σ.support = Finset.univ := Finset.eq_univ_iff_forall.mpr hall'
        rw [huniv, Finset.card_univ] at h2
        exact (Nat.not_even_iff_odd.mpr hcard) (even_iff_two_dvd.mpr h2)
      obtain ⟨i, hi⟩ := hex
      have hfix : σ i = i := Equiv.Perm.notMem_support.mp hi
      have hzero : ∏ j, A (σ j) j = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hfix]; exact hdiag i)
      rw [hzero, smul_zero]
    · intro σ _
      exact Finset.mem_univ _
    · intro σ _
      exact inv_inv σ
  obtain ⟨w, hw0, hAw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hne : ({v | w v ≠ 0} : Set V).Nonempty := by
    by_contra hemp
    apply hw0
    funext v
    by_contra hv
    exact hemp ⟨v, hv⟩
  obtain ⟨ω, hω⟩ := h {v | w v ≠ 0} hne
  have hoddS : Odd (Set.ncard {v : V | w v ≠ 0 ∧ G.Adj ω v}) := hω
  have h1 : ({v : V | w v ≠ 0 ∧ G.Adj ω v} : Set V).toFinset =
      Finset.univ.filter (· ∈ ({v : V | w v ≠ 0 ∧ G.Adj ω v} : Set V)) := by
    ext v
    simp
  have hS : ((Set.ncard {v : V | w v ≠ 0 ∧ G.Adj ω v} : ℕ) : ZMod 2) =
      ∑ v : V, (if v ∈ ({v : V | w v ≠ 0 ∧ G.Adj ω v} : Set V) then (1 : ZMod 2) else 0) := by
    rw [Set.ncard_eq_toFinset_card', h1, ← Finset.sum_filter, Finset.card_eq_sum_ones,
      Nat.cast_sum]
    simp
  have hterm : ∀ v : V,
      (if v ∈ ({v : V | w v ≠ 0 ∧ G.Adj ω v} : Set V) then (1 : ZMod 2) else 0) =
        A ω v * w v := by
    intro v
    have hwv : w v = 0 ∨ w v = 1 := by
      generalize w v = x
      revert x
      decide
    rw [hA]
    rcases hwv with h0 | h1'
    · simp [h0]
    · by_cases hadj : G.Adj ω v <;> simp [h1', hadj]
  have hzero : ∑ v : V, A ω v * w v = 0 := congrFun hAw ω
  rw [Finset.sum_congr rfl (fun v _ => hterm v), hzero] at hS
  have hone := ZMod.natCast_eq_one_iff_odd.mpr hoddS
  rw [hS] at hone
  exact zero_ne_one hone
