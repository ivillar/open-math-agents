import OMAStatements.S_mo_386884
import Mathlib

-- Problem: mo-386884, every finite graph is a strict unit-distance graph in some Euclidean
-- space.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Use coordinates indexed by ordered pairs (a, b) of vertices. Vertex i gets the vector with
-- entry 1 at every (i, b), plus t(a, i) at every (a, i), where t = 1/2 on adjacent pairs and
-- -1/2 otherwise. For i != j the squared distance is (5/2) n - 2 - 4 t(i, j): it takes the
-- value (5/2) n - 4 on edges and (5/2) n on non-edges. Rescaling by the square root of
-- (5/2) n - 4 makes exactly the edges have length 1.

namespace MO386884

noncomputable def t {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : ℝ :=
  if G.Adj a b then 1 / 2 else -1 / 2

noncomputable def Y {V : Type} [DecidableEq V] (i j a : V) : ℝ :=
  (if a = i then 1 else 0) - (if a = j then 1 else 0)

noncomputable def p {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : V) (ab : V × V) : ℝ :=
  (if ab.1 = i then 1 else 0) + (if ab.2 = i then t G ab.1 ab.2 else 0)

theorem t_self {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) :
    t G a a = -1 / 2 := by
  simp [t]

theorem t_symm {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    t G a b = t G b a := by
  unfold t
  by_cases h : G.Adj a b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

theorem t_le {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    t G a b ≤ 1 / 2 := by
  unfold t
  split_ifs <;> norm_num

theorem key {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j : V) (hij : i ≠ j) :
    ∑ ab : V × V, (p G i ab - p G j ab) ^ 2 =
      5 / 2 * (Fintype.card V : ℝ) - 2 - 4 * t G i j := by
  have hY2 : ∀ b : V, Y i j b ^ 2 =
      (if b = i then (1 : ℝ) else 0) + (if b = j then (1 : ℝ) else 0) := by
    intro b
    unfold Y
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) hij
    · norm_num
    · norm_num
    · norm_num
  have L2 : ∑ b : V, Y i j b ^ 2 = 2 := by
    simp only [hY2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    norm_num
  have L3 : ∀ F : V → ℝ, ∑ b : V, Y i j b * F b = F i - F j := by
    intro F
    simp only [Y, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have ht2 : ∀ a b : V, t G a b ^ 2 = 1 / 4 := by
    intro a b
    unfold t
    split_ifs <;> norm_num
  have hsumm : ∀ a b : V, p G i (a, b) - p G j (a, b) = Y i j a + Y i j b * t G a b := by
    intro a b
    simp only [p, Y]
    split_ifs <;> ring
  have hinner : ∀ a : V, ∑ b : V, (p G i (a, b) - p G j (a, b)) ^ 2 =
      (Fintype.card V : ℝ) * Y i j a ^ 2 + 2 * (Y i j a * (t G a i - t G a j)) + 1 / 2 := by
    intro a
    have e1 : ∀ b : V, (p G i (a, b) - p G j (a, b)) ^ 2 =
        Y i j a ^ 2 + 2 * (Y i j a * (Y i j b * t G a b)) + 1 / 4 * Y i j b ^ 2 := by
      intro b
      rw [hsumm, show (Y i j a + Y i j b * t G a b) ^ 2 = Y i j a ^ 2 +
        2 * (Y i j a * (Y i j b * t G a b)) + Y i j b ^ 2 * t G a b ^ 2 by ring, ht2]
      ring
    simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [L3 (t G a), L2]
    ring
  rw [Fintype.sum_prod_type]
  simp only [hinner, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have h3 : ∑ a : V, Y i j a * (t G a i - t G a j) =
      (t G i i - t G i j) - (t G j i - t G j j) :=
    L3 (fun a => t G a i - t G a j)
  rw [h3, L2, t_self, t_self, t_symm G j i]
  ring

end MO386884

theorem OMA.solution : type_of% @OMA.S_mo_386884.main := by
  intro V _ G
  classical
  cases nonempty_fintype V
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ,
      lam = (Real.sqrt (5 / 2 * (Fintype.card V : ℝ) - 4))⁻¹ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : V → EuclideanSpace ℝ (Fin (Fintype.card (V × V))),
      ∀ i k, P i k = lam * MO386884.p G i ((Fintype.equivFin (V × V)).symm k) :=
    ⟨fun i => WithLp.toLp 2
      (fun k => lam * MO386884.p G i ((Fintype.equivFin (V × V)).symm k)), fun i k => rfl⟩
  have hdist : ∀ i j : V, dist (P i) (P j) =
      Real.sqrt (lam ^ 2 * ∑ ab : V × V, (MO386884.p G i ab - MO386884.p G j ab) ^ 2) := by
    intro i j
    rw [EuclideanSpace.dist_eq]
    congr 1
    have h1 : ∀ k : Fin (Fintype.card (V × V)), dist (P i k) (P j k) ^ 2 =
        lam ^ 2 * (MO386884.p G i ((Fintype.equivFin (V × V)).symm k) -
          MO386884.p G j ((Fintype.equivFin (V × V)).symm k)) ^ 2 := by
      intro k
      rw [hP, hP, Real.dist_eq, sq_abs]
      ring
    have h2 : ∑ k : Fin (Fintype.card (V × V)),
        (MO386884.p G i ((Fintype.equivFin (V × V)).symm k) -
          MO386884.p G j ((Fintype.equivFin (V × V)).symm k)) ^ 2 =
        ∑ ab : V × V, (MO386884.p G i ab - MO386884.p G j ab) ^ 2 :=
      Equiv.sum_comp (Fintype.equivFin (V × V)).symm
        (fun ab => (MO386884.p G i ab - MO386884.p G j ab) ^ 2)
    rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Finset.mul_sum, h2]
  have hfacts : ∀ u v : V, u ≠ v → (0 : ℝ) < 5 / 2 * (Fintype.card V : ℝ) - 4 ∧
      lam ^ 2 = (5 / 2 * (Fintype.card V : ℝ) - 4)⁻¹ := by
    intro u v huv
    have h2 : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨u, v, huv⟩
    have hc : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h2
    have hA : (0 : ℝ) < 5 / 2 * (Fintype.card V : ℝ) - 4 := by linarith
    refine ⟨hA, ?_⟩
    rw [hlam, inv_pow, Real.sq_sqrt hA.le]
  refine ⟨Fintype.card (V × V), P, ?_, ?_⟩
  · intro u v huv
    by_contra hne
    obtain ⟨hA, hlam2⟩ := hfacts u v hne
    have hd := hdist u v
    rw [huv, dist_self, MO386884.key G u v hne, hlam2] at hd
    have ht := MO386884.t_le G u v
    have hpos : 0 < (5 / 2 * (Fintype.card V : ℝ) - 4)⁻¹ *
        (5 / 2 * (Fintype.card V : ℝ) - 2 - 4 * MO386884.t G u v) :=
      mul_pos (inv_pos.mpr hA) (by linarith)
    have hsq := Real.sqrt_pos.mpr hpos
    linarith
  · intro u v huv
    obtain ⟨hA, hlam2⟩ := hfacts u v huv
    rw [hdist, Real.sqrt_eq_one, MO386884.key G u v huv, hlam2, inv_mul_eq_one₀ hA.ne']
    constructor
    · intro hadj
      have ht : MO386884.t G u v = 1 / 2 := by simp [MO386884.t, hadj]
      rw [ht]
      ring
    · intro h
      by_contra hadj
      have ht : MO386884.t G u v = -1 / 2 := by simp [MO386884.t, hadj]
      rw [ht] at h
      linarith
