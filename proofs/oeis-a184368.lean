import OMAStatements.S_oeis_a184368
import Mathlib

-- Proof of the conjectures in OEIS A184368 (statement by @ivillar).
-- Idea: the subblock condition involves only consecutive rows, so the count is a walk count on rows
-- (transfer matrix). A constant row can be followed by any of the 9 rows (3 constant), and a
-- nonconstant row by 6 rows (3 constant, 3 nonconstant). So N(n) = 3α(n) + 6β(n) with
-- α' = 3α + 6β and β' = 3α + 3β, i.e. a(n) = α(n) + 2β(n). The characteristic polynomial t^2 - 6t - 9
-- has roots 3 ± 3*sqrt(2), which gives the recurrence, the g.f. and the closed form.

namespace OMAA184368Helpers

open OMA.S_oeis_a184368

instance (u v : Fin 2 → Fin 3) : Decidable (BlockOK u v) := by unfold BlockOK; infer_instance

abbrev R := Fin 2 → Fin 3

/-- Rows are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Consecutive rows r, s: the subblock they form satisfies the condition. -/
abbrev compat (r s : R) : Prop := BlockOK r s

abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    Fin.succ_zero_eq_one, ← Fin.succ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h2, h4⟩
    simpa using h3
  · rintro ⟨h1, h3, h2, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, h4⟩
    simpa using h3

def F (n : ℕ) (s : R) : ℕ := ∑ y : Fin (n + 1) → R, if Walk y ∧ y 0 = s then 1 else 0

theorem F_zero (s : R) : F 0 s = if ok s then 1 else 0 := by
  unfold F
  rw [← (Equiv.funUnique (Fin 1) R).symm.sum_comp]
  have h : ∀ r : R, (if Walk ((Equiv.funUnique (Fin 1) R).symm r) ∧
      (Equiv.funUnique (Fin 1) R).symm r 0 = s then 1 else 0) = if r = s then (if ok s then 1 else 0) else 0 := by
    intro r
    simp only [Equiv.funUnique_symm_apply, Walk, IsEmpty.forall_iff, and_true]
    by_cases hr : r = s
    · subst hr; simp
    · simp [hr]
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq']
  simp

theorem F_succ (n : ℕ) (s : R) :
    F (n + 1) s = ∑ t : R, if ok s ∧ compat s t then F n t else 0 := by
  have lhs : F (n + 1) s = ∑ y : Fin (n + 1) → R, if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0 := by
    unfold F
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => R)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have h : ∀ r : R, (if Walk ((Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y)) ∧
        (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) 0 = s then 1 else 0) =
        if r = s then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
      intro r
      rw [show (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) = (Fin.cons r y : Fin (n + 2) → R)
        from rfl]
      simp only [walk_cons, Fin.cons_zero]
      by_cases hr : r = s
      · subst hr
        rw [if_pos rfl]
        exact if_congr ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩ rfl rfl
      · rw [if_neg hr, if_neg (show ¬((ok r ∧ compat r (y 0) ∧ Walk y) ∧ r = s) from fun h => hr h.2)]
    rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [lhs]
  unfold F
  have h2 : ∀ t : R, (if ok s ∧ compat s t then
      ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = t then 1 else 0) else 0) =
      ∑ y : Fin (n + 1) → R, if y 0 = t then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
    intro t
    split_ifs with ht
    · apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y 0 = t
      · subst hy
        rw [if_pos (rfl : y 0 = y 0)]
        exact if_congr ⟨fun h => ⟨ht.1, ht.2, h.1⟩, fun h => ⟨h.2.2, rfl⟩⟩ rfl rfl
      · rw [if_neg hy, if_neg (show ¬(Walk y ∧ y 0 = t) from fun h => hy h.2)]
    · symm
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y 0 = t
      · subst hy; rw [if_pos rfl, if_neg (fun h => ht ⟨h.1, h.2.1⟩)]
      · rw [if_neg hy]
  rw [Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- Walk counts from a constant row (α) and from a nonconstant row (β). -/
def α : ℕ → ℕ
  | 0 => 1
  | n + 1 => 3 * α n + 6 * β n
where
  β : ℕ → ℕ
  | 0 => 1
  | n + 1 => 3 * α n + 3 * β n

abbrev Z (t : R) : Prop := t 0 = t 1

def V (n : ℕ) (s : R) : ℕ := if Z s then α n else α.β n

theorem cA : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ Z t)).card =
    if Z s then 3 else 3 := by decide

theorem cB : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t)).card =
    if Z s then 6 else 3 := by decide

theorem tA : (Finset.univ.filter (fun t : R => True ∧ Z t)).card = 3 := by decide
theorem tB : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t)).card = 6 := by decide

theorem split_V (n : ℕ) (P : Prop) [Decidable P] (t : R) :
    (if P then V n t else 0) = (if P ∧ Z t then α n else 0) + (if P ∧ ¬ Z t then α.β n else 0) := by
  unfold V
  by_cases h1 : P
  · rw [if_pos h1]
    by_cases h2 : Z t
    · rw [if_pos h2, if_pos (show P ∧ Z t from ⟨h1, h2⟩),
        if_neg (show ¬(P ∧ ¬ Z t) from fun h => h.2 h2)]
      ring
    · rw [if_neg h2, if_neg (show ¬(P ∧ Z t) from fun h => h2 h.2),
        if_pos (show P ∧ ¬ Z t from ⟨h1, h2⟩)]
      ring
  · rw [if_neg h1, if_neg (show ¬(P ∧ Z t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t) from fun h => h1 h.1)]

theorem sum_V (n : ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then V n t else 0) =
      (Finset.univ.filter (fun t => P t ∧ Z t)).card * α n +
      (Finset.univ.filter (fun t => P t ∧ ¬ Z t)).card * α.β n := by
  rw [Finset.sum_congr rfl (fun t _ => split_V n (P t) t), Finset.sum_add_distrib,
    Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const, Finset.sum_const_zero, smul_eq_mul, add_zero, mul_zero]

theorem F_eq (n : ℕ) : ∀ s : R, F n s = V n s := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    unfold V
    simp only [ok, if_true]
    split_ifs <;> rfl
  | succ n ih =>
    intro s
    rw [F_succ]
    simp only [ih]
    rw [sum_V n (fun t => ok s ∧ compat s t), cA s, cB s]
    unfold V
    split_ifs <;> simp [α, α.β]

theorem N_eq (n : ℕ) : N n = 3 * α n + 6 * α.β n := by
  unfold N
  rw [Nat.card_congr (Equiv.subtypeEquivRight
      (p := fun x : Fin (n + 1) → R => ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ))
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => ⟨fun h => ⟨fun _ => trivial, h⟩, fun h => h.2⟩)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, if True then F n s else 0 := by
    unfold F
    simp only [if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have hh : ∀ s : R, (if Walk y ∧ y 0 = s then 1 else 0) = if y 0 = s then (if Walk y then 1 else 0) else 0 := by
      intro s
      by_cases h : y 0 = s
      · rw [if_pos h]; exact if_congr ⟨fun hh => hh.1, fun hh => ⟨hh, h⟩⟩ rfl rfl
      · rw [if_neg h, if_neg (show ¬(Walk y ∧ y 0 = s) from fun hh => h hh.2)]
    rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [h1]
  simp only [F_eq]
  rw [sum_V n (fun _ => True), tA, tB]

theorem a_eq (n : ℕ) : a n = α n + 2 * α.β n := by
  unfold a
  rw [N_eq, show 3 * α n + 6 * α.β n = 3 * (α n + 2 * α.β n) by ring, Nat.mul_div_cancel_left _ (by norm_num)]

theorem a_rec (n : ℕ) : a (n + 2) = 6 * a (n + 1) + 9 * a n := by
  rw [a_eq, a_eq, a_eq]
  simp only [α, α.β]
  ring

theorem a_one : a 1 = 21 := by rw [a_eq]; simp [α, α.β]
theorem a_two : a 2 = 153 := by rw [a_eq]; simp [α, α.β]

theorem closedT (k : ℕ) :
    2 * Real.sqrt 2 * (a (k + 1) : ℝ) = (3 - 3 * Real.sqrt 2) ^ (k + 1) * (-4 + 3 * Real.sqrt 2) +
      (3 * (1 + Real.sqrt 2)) ^ (k + 1) * (4 + 3 * Real.sqrt 2) ∧
    2 * Real.sqrt 2 * (a (k + 2) : ℝ) = (3 - 3 * Real.sqrt 2) ^ (k + 2) * (-4 + 3 * Real.sqrt 2) +
      (3 * (1 + Real.sqrt 2)) ^ (k + 2) * (4 + 3 * Real.sqrt 2) := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have r1 : (3 * (1 + Real.sqrt 2)) ^ 2 = 6 * (3 * (1 + Real.sqrt 2)) + 9 := by linear_combination 9 * hs
  have r2 : (3 - 3 * Real.sqrt 2) ^ 2 = 6 * (3 - 3 * Real.sqrt 2) + 9 := by linear_combination 9 * hs
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a_one]; push_cast; linear_combination (0 : ℝ) * hs
    · rw [a_two]; push_cast; linear_combination (-54 * Real.sqrt 2) * hs
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h : ((a (k + 3) : ℕ) : ℝ) = ((6 * a (k + 2) + 9 * a (k + 1) : ℕ) : ℝ) := by rw [a_rec]
    push_cast at h
    rw [show k + 1 + 2 = k + 3 from rfl, h]
    obtain ⟨h1, h2⟩ := ih
    linear_combination (6 : ℝ) * h2 + (9 : ℝ) * h1 -
      (3 - 3 * Real.sqrt 2) ^ (k + 1) * (-4 + 3 * Real.sqrt 2) * r2 -
      (3 * (1 + Real.sqrt 2)) ^ (k + 1) * (4 + 3 * Real.sqrt 2) * r1

end OMAA184368Helpers

open OMA.S_oeis_a184368 OMAA184368Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a184368.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    exact a_rec (k + 1)
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * (1 - 6 * PowerSeries.X - 9 * PowerSeries.X ^ 2) =
        F' - PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 1 * F') -
          PowerSeries.C (9 : ℚ) * (PowerSeries.X ^ 2 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (3 * PowerSeries.X * (7 + 9 * PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.C (21 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (27 : ℚ) * PowerSeries.X ^ 2 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 2
    · interval_cases n <;> norm_num [a_one, a_two]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
      have h := a_rec (j + 1)
      have q : ((a (j + 3) : ℕ) : ℚ) = ((6 * a (j + 2) + 9 * a (j + 1) : ℕ) : ℚ) := by rw [h]
      push_cast at q
      simp
      linear_combination q
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h := (closedT k).1
    have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [eq_div_iff (by positivity), ← h]
    ring
