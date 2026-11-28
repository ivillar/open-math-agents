import OMAStatements.S_oeis_a235888
import Mathlib

-- Proof of the conjectures in OEIS A235888 (statement by @ivillar).
-- Idea: the subblock conditions involve only consecutive rows, so the count is a walk count on rows
-- (transfer matrix). Checking all row pairs:
-- * a constant row has exactly 4 successors (the constant rows);
-- * a row with exactly two distinct values has 2 successors, of the same kind;
-- * a row with at least three values has 1 successor, of the same kind.
-- Hence a(n) = 4*4^n + 84*2^n + 168 = 4*(42 + 21*2^n + 4^n), and the recurrence and g.f. follow.

namespace OMAA235888Helpers

open OMA.S_oeis_a235888

instance (u v : Fin 4 → Fin 4) : Decidable (BlockOK u v) := by
  unfold BlockOK Med4; infer_instance

abbrev R := Fin 4 → Fin 4

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

/-- Walk counts by row type: 3^n, 2^n or 1 (each class is closed under succession). -/
def f : ℕ → ℕ
  | 0 => 1
  | n + 1 => 4 * f n
where
  g : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * g n
  h : ℕ → ℕ
  | 0 => 1
  | n + 1 => h n

abbrev Z (t : R) : Prop := t 0 = t 1 ∧ t 1 = t 2 ∧ t 2 = t 3
abbrev O (t : R) : Prop := (Finset.univ.image t).card ≤ 2

def V (n : ℕ) (s : R) : ℕ := if Z s then f n else if O s then f.g n else f.h n

theorem cZ : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ Z t)).card =
    if Z s then 4 else 0 := by decide +kernel

theorem cO : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ O t)).card =
    if Z s then 0 else if O s then 2 else 0 := by decide +kernel

theorem cN : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ ¬ O t)).card =
    if Z s then 0 else if O s then 0 else 1 := by decide +kernel

theorem tZ : (Finset.univ.filter (fun t : R => True ∧ Z t)).card = 4 := by decide +kernel
theorem tO : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ O t)).card = 84 := by decide +kernel
theorem tN : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ ¬ O t)).card = 168 := by decide +kernel

theorem split_V (n : ℕ) (P : Prop) [Decidable P] (t : R) :
    (if P then V n t else 0) = ((if P ∧ Z t then f n else 0) +
      (if P ∧ ¬ Z t ∧ O t then f.g n else 0)) + (if P ∧ ¬ Z t ∧ ¬ O t then f.h n else 0) := by
  unfold V
  by_cases h1 : P
  · rw [if_pos h1]
    by_cases h2 : Z t
    · rw [if_pos h2, if_pos (show P ∧ Z t from ⟨h1, h2⟩),
        if_neg (show ¬(P ∧ ¬ Z t ∧ O t) from fun h => h.2.1 h2),
        if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ O t) from fun h => h.2.1 h2)]
      ring
    · rw [if_neg h2, if_neg (show ¬(P ∧ Z t) from fun h => h2 h.2)]
      by_cases h3 : O t
      · rw [if_pos h3, if_pos (show P ∧ ¬ Z t ∧ O t from ⟨h1, h2, h3⟩),
          if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ O t) from fun h => h.2.2 h3)]
        ring
      · rw [if_neg h3, if_neg (show ¬(P ∧ ¬ Z t ∧ O t) from fun h => h3 h.2.2),
          if_pos (show P ∧ ¬ Z t ∧ ¬ O t from ⟨h1, h2, h3⟩)]
        ring
  · rw [if_neg h1, if_neg (show ¬(P ∧ Z t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t ∧ O t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ O t) from fun h => h1 h.1)]

theorem sum_V (n : ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then V n t else 0) =
      (Finset.univ.filter (fun t => P t ∧ Z t)).card * f n +
      (Finset.univ.filter (fun t => P t ∧ ¬ Z t ∧ O t)).card * f.g n +
      (Finset.univ.filter (fun t => P t ∧ ¬ Z t ∧ ¬ O t)).card * f.h n := by
  rw [Finset.sum_congr rfl (fun t _ => split_V n (P t) t), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_ite]
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
    rw [sum_V n (fun t => ok s ∧ compat s t), cZ s, cO s, cN s]
    unfold V
    split_ifs <;> simp [f, f.g, f.h] <;> ring

theorem a_eq (n : ℕ) : a n = 4 * f n + 84 * f.g n + 168 * f.h n := by
  unfold a
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
  rw [sum_V n (fun _ => True), tZ, tO, tN]

theorem f_pow (n : ℕ) : f n = 4 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [f, ih]; ring

theorem g_pow (n : ℕ) : f.g n = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [f.g, ih]; ring

theorem h_one (n : ℕ) : f.h n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [f.h, ih]

theorem a_closed (n : ℕ) : a n = 4 * 4 ^ n + 84 * 2 ^ n + 168 := by
  rw [a_eq, f_pow, g_pow, h_one]
  try ring

end OMAA235888Helpers

open OMA.S_oeis_a235888 OMAA235888Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a235888.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega, a_closed, a_closed, a_closed, a_closed]
    push_cast
    ring
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
        F' - PowerSeries.C (7 : ℚ) * (PowerSeries.X ^ 1 * F') +
          PowerSeries.C (14 : ℚ) * (PowerSeries.X ^ 2 * F') -
          PowerSeries.C (8 : ℚ) * (PowerSeries.X ^ 3 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (8 * PowerSeries.X * (44 - 237 * PowerSeries.X + 256 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (352 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (1896 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (2048 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 3
    · interval_cases n <;> norm_num [a_closed]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
      simp [a_closed]
      ring
  · rw [a_closed]
    ring
