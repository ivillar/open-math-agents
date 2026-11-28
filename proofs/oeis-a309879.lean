import OMAStatements.S_oeis_a309879
import Mathlib

/-!
# A309879: Barker's recurrence

Adding 1 to every part maps the partitions of m into 5 parts onto those of m + 5 with smallest part
at least 2 and flips the parity of the second smallest part; the partitions with smallest part 1
are 1 + (a partition of m + 4 into 4 parts), whose second smallest part is the smallest part of
that partition. With OK, EK the numbers of partitions into 5 parts with odd, even second smallest
part, OS, ES the numbers of partitions into 4 parts with odd, even smallest part and N3 the number
of partitions into 3 parts:
OK(m + 5) = EK(m) + OS(m + 4), EK(m + 5) = OK(m) + ES(m + 4), OS(r + 4) = ES(r) + N3(r + 3),
ES(r + 4) = OS(r), N3(r + 3) = N3(r) + N2(r) and N2(r + 1) + N2(r) = r + 2 with
N2(r) = floor((r + 2)/2). Barker's operator applied to OK is an explicit integer combination of
these relations.
-/

namespace PA309879

theorem icc_range (m : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 m, f k = ∑ t ∈ Finset.range m, f (t + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem icc_range' (k X : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc k X, f i = ∑ j ∈ Finset.range (X + 1 - k), f (k + j) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]

/-- Weighted sum over the partitions `j + i + (r - i - j)` of `r` with fixed smallest part `j`. -/
def I3 (w : ℕ → ℕ → ℕ → ℕ) (r j : ℕ) : ℕ :=
  ∑ u ∈ Finset.range ((r - j) / 2 + 1 - j), w j (j + u) (r - (j + u) - j)

/-- Weighted sum over the partitions of `r` into 3 parts, all at least `k`. -/
def H3 (w : ℕ → ℕ → ℕ → ℕ) (r k : ℕ) : ℕ :=
  ∑ s ∈ Finset.range (r / 3 + 1 - k), I3 w r (k + s)

/-- Weighted sum over the partitions of `r` into 4 parts, all at least `l`. -/
def H4L (W : ℕ → ℕ → ℕ → ℕ → ℕ) (r l : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (r / 4 + 1 - l), H3 (W (l + t)) (r - (l + t)) (l + t)

/-- Weighted sum over the partitions of `m` into 5 parts. -/
def H5 (V : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (m / 5), H4L (V (t + 1)) (m - (t + 1)) (t + 1)

theorem I3_shift (w : ℕ → ℕ → ℕ → ℕ) (r j : ℕ) :
    I3 w (r + 3) (j + 1) = I3 (fun x y z => w (x + 1) (y + 1) (z + 1)) r j := by
  unfold I3
  rw [show (r + 3 - (j + 1)) / 2 + 1 - (j + 1) = (r - j) / 2 + 1 - j by omega]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_range] at hu
  rw [show r + 3 - (j + 1 + u) - (j + 1) = r - (j + u) - j + 1 by omega,
    show j + 1 + u = j + u + 1 by omega]

theorem H3_shift (w : ℕ → ℕ → ℕ → ℕ) (r k : ℕ) :
    H3 w (r + 3) (k + 1) = H3 (fun x y z => w (x + 1) (y + 1) (z + 1)) r k := by
  unfold H3
  rw [show (r + 3) / 3 + 1 - (k + 1) = r / 3 + 1 - k by omega]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show k + 1 + s = k + s + 1 by omega]
  exact I3_shift w r (k + s)

theorem H3_peel (w : ℕ → ℕ → ℕ → ℕ) (r : ℕ) :
    H3 w (r + 3) 1 = H3 (fun x y z => w (x + 1) (y + 1) (z + 1)) r 1 + I3 w (r + 3) 1 := by
  unfold H3
  rw [show (r + 3) / 3 + 1 - 1 = r / 3 + 1 - 1 + 1 by omega, Finset.sum_range_succ',
    Nat.add_zero]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show 1 + (s + 1) = 1 + s + 1 by omega]
  exact I3_shift w r (1 + s)

theorem H4L_shift (W : ℕ → ℕ → ℕ → ℕ → ℕ) (r l : ℕ) :
    H4L W (r + 4) (l + 1) = H4L (fun k x y z => W (k + 1) (x + 1) (y + 1) (z + 1)) r l := by
  unfold H4L
  rw [show (r + 4) / 4 + 1 - (l + 1) = r / 4 + 1 - l by omega]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [show r + 4 - (l + 1 + t) = r - (l + t) + 3 by omega, show l + 1 + t = l + t + 1 by omega]
  exact H3_shift (W (l + t + 1)) (r - (l + t)) (l + t)

theorem H4L_peel (W : ℕ → ℕ → ℕ → ℕ → ℕ) (r : ℕ) :
    H4L W (r + 4) 1 = H4L (fun k x y z => W (k + 1) (x + 1) (y + 1) (z + 1)) r 1 +
      H3 (W 1) (r + 3) 1 := by
  unfold H4L
  rw [show (r + 4) / 4 + 1 - 1 = r / 4 + 1 - 1 + 1 by omega, Finset.sum_range_succ',
    Nat.add_zero, show r + 4 - 1 = r + 3 by omega]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [show r + 4 - (1 + (t + 1)) = r - (1 + t) + 3 by omega, show 1 + (t + 1) = 1 + t + 1 by omega]
  exact H3_shift (W (1 + t + 1)) (r - (1 + t)) (1 + t)

theorem H5_shift (V : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (m : ℕ) :
    H5 V (m + 5) = H5 (fun l k x y z => V (l + 1) (k + 1) (x + 1) (y + 1) (z + 1)) m +
      H4L (V 1) (m + 4) 1 := by
  unfold H5
  rw [show (m + 5) / 5 = m / 5 + 1 by omega, Finset.sum_range_succ',
    show m + 5 - (0 + 1) = m + 4 by omega]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [show m + 5 - (t + 1 + 1) = m - (t + 1) + 4 by omega]
  exact H4L_shift (V (t + 1 + 1)) (m - (t + 1)) (t + 1)

theorem H3_congr (w w' : ℕ → ℕ → ℕ → ℕ) (r k : ℕ) (h : ∀ x y z, w x y z = w' x y z) :
    H3 w r k = H3 w' r k := by
  rw [show w = w' from funext fun x => funext fun y => funext fun z => h x y z]

theorem H4L_congr (W W' : ℕ → ℕ → ℕ → ℕ → ℕ) (r l : ℕ)
    (h : ∀ k x y z, W k x y z = W' k x y z) : H4L W r l = H4L W' r l := by
  rw [show W = W' from funext fun k => funext fun x => funext fun y => funext fun z => h k x y z]

theorem H5_congr (V V' : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (m : ℕ)
    (h : ∀ l k x y z, V l k x y z = V' l k x y z) : H5 V m = H5 V' m := by
  rw [show V = V' from funext fun l => funext fun k => funext fun x => funext fun y =>
    funext fun z => h l k x y z]

theorem H3_add (f g : ℕ → ℕ → ℕ → ℕ) (r k : ℕ) :
    H3 (fun x y z => f x y z + g x y z) r k = H3 f r k + H3 g r k := by
  unfold H3 I3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]

theorem H4L_add (F G : ℕ → ℕ → ℕ → ℕ → ℕ) (r l : ℕ) :
    H4L (fun k x y z => F k x y z + G k x y z) r l = H4L F r l + H4L G r l := by
  unfold H4L
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => H3_add (F (l + t)) (G (l + t)) _ _

theorem H5_add (F G : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (m : ℕ) :
    H5 (fun l k x y z => F l k x y z + G l k x y z) m = H5 F m + H5 G m := by
  unfold H5
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => H4L_add (F (t + 1)) (G (t + 1)) _ _

theorem H3_zero (r k : ℕ) : H3 (fun _ _ _ => 0) r k = 0 := by
  unfold H3 I3
  simp only [Finset.sum_const_zero]

def N5 (m : ℕ) : ℕ := H5 (fun _ _ _ _ _ => 1) m

def N4 (r : ℕ) : ℕ := H4L (fun _ _ _ _ => 1) r 1

def N3 (r : ℕ) : ℕ := H3 (fun _ _ _ => 1) r 1

def N2 (r : ℕ) : ℕ := (r + 2) / 2

theorem relR5 (m : ℕ) : N5 (m + 5) = N5 m + N4 (m + 4) := by
  unfold N5 N4
  rw [H5_shift]

theorem relR4 (r : ℕ) : N4 (r + 4) = N4 r + N3 (r + 3) := by
  unfold N4 N3
  rw [H4L_peel]

theorem relR3 (r : ℕ) : N3 (r + 3) = N3 r + N2 r := by
  unfold N3 N2
  rw [H3_peel]
  congr 1
  unfold I3
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  omega

theorem relR2 (t : ℕ) : N2 (t + 1) + N2 t = t + 2 := by
  unfold N2
  omega

def OK (m : ℕ) : ℕ := H5 (fun _ k _ _ _ => k % 2) m

def EK (m : ℕ) : ℕ := H5 (fun _ k _ _ _ => (k + 1) % 2) m

def OS (r : ℕ) : ℕ := H4L (fun k _ _ _ => k % 2) r 1

def ES (r : ℕ) : ℕ := H4L (fun k _ _ _ => (k + 1) % 2) r 1

theorem relOK (m : ℕ) : OK (m + 5) = EK m + OS (m + 4) := by
  unfold OK EK OS
  rw [H5_shift]

theorem relEK (m : ℕ) : EK (m + 5) = OK m + ES (m + 4) := by
  unfold OK EK ES
  rw [H5_shift, H5_congr _ (fun _ k _ _ _ => k % 2) m (fun l k x y z => by omega)]

theorem relOS (r : ℕ) : OS (r + 4) = ES r + N3 (r + 3) := by
  unfold OS ES N3
  rw [H4L_peel, H3_congr _ (fun _ _ _ => 1) (r + 3) 1 (fun x y z => by omega)]

theorem relES (r : ℕ) : ES (r + 4) = OS r := by
  unfold OS ES
  rw [H4L_peel, H4L_congr _ (fun k _ _ _ => k % 2) r 1 (fun k x y z => by omega),
    H3_congr _ (fun _ _ _ => 0) (r + 3) 1 (fun x y z => by omega), H3_zero, Nat.add_zero]

theorem a_eq (n : ℕ) : OMA.S_oeis_a309879.a n = OK n := by
  unfold OMA.S_oeis_a309879.a OK H5
  rw [icc_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold H4L
  rw [icc_range']
  refine Finset.sum_congr rfl fun s1 _ => ?_
  unfold H3
  rw [icc_range', show (n - (t + 1 + s1) - (t + 1)) / 3 + 1 - (t + 1 + s1) =
    (n - (t + 1) - (t + 1 + s1)) / 3 + 1 - (t + 1 + s1) by omega]
  refine Finset.sum_congr rfl fun s2 _ => ?_
  unfold I3
  rw [icc_range', show (n - (t + 1 + s1 + s2) - (t + 1 + s1) - (t + 1)) / 2 + 1 - (t + 1 + s1 + s2) =
    (n - (t + 1) - (t + 1 + s1) - (t + 1 + s1 + s2)) / 2 + 1 - (t + 1 + s1 + s2) by omega]

end PA309879

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a309879.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 23 := ⟨n - 23, by omega⟩
  simp only [show m + 23 - 1 = m + 22 by omega, show m + 23 - 2 = m + 21 by omega, show m + 23 - 3 = m +
    20 by omega, show m + 23 - 4 = m + 19 by omega, show m + 23 - 5 = m + 18 by omega, show m +
    23 - 8 = m + 15 by omega, show m + 23 - 9 = m + 14 by omega, show m + 23 - 10 = m + 13 by
    omega, show m + 23 - 11 = m + 12 by omega, show m + 23 - 12 = m + 11 by omega, show m + 23 -
    13 = m + 10 by omega, show m + 23 - 14 = m + 9 by omega, show m + 23 - 15 = m + 8 by omega,
    show m + 23 - 18 = m + 5 by omega, show m + 23 - 19 = m + 4 by omega, show m + 23 - 20 = m +
    3 by omega, show m + 23 - 21 = m + 2 by omega, show m + 23 - 22 = m + 1 by omega, show m +
    23 - 23 = m by omega, PA309879.a_eq]
  have hEK_0 : (PA309879.EK (m + 5) : ℤ) = PA309879.OK (m) + PA309879.ES (m + 4) := by
    exact_mod_cast PA309879.relEK (m)
  have hEK_1 : (PA309879.EK (m + 6) : ℤ) = PA309879.OK (m + 1) + PA309879.ES (m + 5) := by
    exact_mod_cast PA309879.relEK (m + 1)
  have hEK_2 : (PA309879.EK (m + 7) : ℤ) = PA309879.OK (m + 2) + PA309879.ES (m + 6) := by
    exact_mod_cast PA309879.relEK (m + 2)
  have hEK_3 : (PA309879.EK (m + 8) : ℤ) = PA309879.OK (m + 3) + PA309879.ES (m + 7) := by
    exact_mod_cast PA309879.relEK (m + 3)
  have hEK_4 : (PA309879.EK (m + 9) : ℤ) = PA309879.OK (m + 4) + PA309879.ES (m + 8) := by
    exact_mod_cast PA309879.relEK (m + 4)
  have hEK_5 : (PA309879.EK (m + 10) : ℤ) = PA309879.OK (m + 5) + PA309879.ES (m + 9) := by
    exact_mod_cast PA309879.relEK (m + 5)
  have hEK_8 : (PA309879.EK (m + 13) : ℤ) = PA309879.OK (m + 8) + PA309879.ES (m + 12) := by
    exact_mod_cast PA309879.relEK (m + 8)
  have hEK_9 : (PA309879.EK (m + 14) : ℤ) = PA309879.OK (m + 9) + PA309879.ES (m + 13) := by
    exact_mod_cast PA309879.relEK (m + 9)
  have hEK_10 : (PA309879.EK (m + 15) : ℤ) = PA309879.OK (m + 10) + PA309879.ES (m + 14) := by
    exact_mod_cast PA309879.relEK (m + 10)
  have hEK_11 : (PA309879.EK (m + 16) : ℤ) = PA309879.OK (m + 11) + PA309879.ES (m + 15) := by
    exact_mod_cast PA309879.relEK (m + 11)
  have hEK_12 : (PA309879.EK (m + 17) : ℤ) = PA309879.OK (m + 12) + PA309879.ES (m + 16) := by
    exact_mod_cast PA309879.relEK (m + 12)
  have hEK_13 : (PA309879.EK (m + 18) : ℤ) = PA309879.OK (m + 13) + PA309879.ES (m + 17) := by
    exact_mod_cast PA309879.relEK (m + 13)
  have hES_8 : (PA309879.ES (m + 12) : ℤ) = PA309879.OS (m + 8) := by
    exact_mod_cast PA309879.relES (m + 8)
  have hES_9 : (PA309879.ES (m + 13) : ℤ) = PA309879.OS (m + 9) := by
    exact_mod_cast PA309879.relES (m + 9)
  have hES_10 : (PA309879.ES (m + 14) : ℤ) = PA309879.OS (m + 10) := by
    exact_mod_cast PA309879.relES (m + 10)
  have hES_12 : (PA309879.ES (m + 16) : ℤ) = PA309879.OS (m + 12) := by
    exact_mod_cast PA309879.relES (m + 12)
  have hES_13 : (PA309879.ES (m + 17) : ℤ) = PA309879.OS (m + 13) := by
    exact_mod_cast PA309879.relES (m + 13)
  have hES_14 : (PA309879.ES (m + 18) : ℤ) = PA309879.OS (m + 14) := by
    exact_mod_cast PA309879.relES (m + 14)
  have hOK_5 : (PA309879.OK (m + 10) : ℤ) = PA309879.EK (m + 5) + PA309879.OS (m + 9) := by
    exact_mod_cast PA309879.relOK (m + 5)
  have hOK_6 : (PA309879.OK (m + 11) : ℤ) = PA309879.EK (m + 6) + PA309879.OS (m + 10) := by
    exact_mod_cast PA309879.relOK (m + 6)
  have hOK_7 : (PA309879.OK (m + 12) : ℤ) = PA309879.EK (m + 7) + PA309879.OS (m + 11) := by
    exact_mod_cast PA309879.relOK (m + 7)
  have hOK_8 : (PA309879.OK (m + 13) : ℤ) = PA309879.EK (m + 8) + PA309879.OS (m + 12) := by
    exact_mod_cast PA309879.relOK (m + 8)
  have hOK_9 : (PA309879.OK (m + 14) : ℤ) = PA309879.EK (m + 9) + PA309879.OS (m + 13) := by
    exact_mod_cast PA309879.relOK (m + 9)
  have hOK_10 : (PA309879.OK (m + 15) : ℤ) = PA309879.EK (m + 10) + PA309879.OS (m + 14) := by
    exact_mod_cast PA309879.relOK (m + 10)
  have hOK_13 : (PA309879.OK (m + 18) : ℤ) = PA309879.EK (m + 13) + PA309879.OS (m + 17) := by
    exact_mod_cast PA309879.relOK (m + 13)
  have hOK_14 : (PA309879.OK (m + 19) : ℤ) = PA309879.EK (m + 14) + PA309879.OS (m + 18) := by
    exact_mod_cast PA309879.relOK (m + 14)
  have hOK_15 : (PA309879.OK (m + 20) : ℤ) = PA309879.EK (m + 15) + PA309879.OS (m + 19) := by
    exact_mod_cast PA309879.relOK (m + 15)
  have hOK_16 : (PA309879.OK (m + 21) : ℤ) = PA309879.EK (m + 16) + PA309879.OS (m + 20) := by
    exact_mod_cast PA309879.relOK (m + 16)
  have hOK_17 : (PA309879.OK (m + 22) : ℤ) = PA309879.EK (m + 17) + PA309879.OS (m + 21) := by
    exact_mod_cast PA309879.relOK (m + 17)
  have hOK_18 : (PA309879.OK (m + 23) : ℤ) = PA309879.EK (m + 18) + PA309879.OS (m + 22) := by
    exact_mod_cast PA309879.relOK (m + 18)
  have hOS_4 : (PA309879.OS (m + 8) : ℤ) = PA309879.ES (m + 4) + PA309879.N3 (m + 7) := by
    exact_mod_cast PA309879.relOS (m + 4)
  have hOS_5 : (PA309879.OS (m + 9) : ℤ) = PA309879.ES (m + 5) + PA309879.N3 (m + 8) := by
    exact_mod_cast PA309879.relOS (m + 5)
  have hOS_6 : (PA309879.OS (m + 10) : ℤ) = PA309879.ES (m + 6) + PA309879.N3 (m + 9) := by
    exact_mod_cast PA309879.relOS (m + 6)
  have hOS_7 : (PA309879.OS (m + 11) : ℤ) = PA309879.ES (m + 7) + PA309879.N3 (m + 10) := by
    exact_mod_cast PA309879.relOS (m + 7)
  have hOS_8 : (PA309879.OS (m + 12) : ℤ) = PA309879.ES (m + 8) + PA309879.N3 (m + 11) := by
    exact_mod_cast PA309879.relOS (m + 8)
  have hOS_9 : (PA309879.OS (m + 13) : ℤ) = PA309879.ES (m + 9) + PA309879.N3 (m + 12) := by
    exact_mod_cast PA309879.relOS (m + 9)
  have hOS_13 : (PA309879.OS (m + 17) : ℤ) = PA309879.ES (m + 13) + PA309879.N3 (m + 16) := by
    exact_mod_cast PA309879.relOS (m + 13)
  have hOS_14 : (PA309879.OS (m + 18) : ℤ) = PA309879.ES (m + 14) + PA309879.N3 (m + 17) := by
    exact_mod_cast PA309879.relOS (m + 14)
  have hOS_15 : (PA309879.OS (m + 19) : ℤ) = PA309879.ES (m + 15) + PA309879.N3 (m + 18) := by
    exact_mod_cast PA309879.relOS (m + 15)
  have hOS_16 : (PA309879.OS (m + 20) : ℤ) = PA309879.ES (m + 16) + PA309879.N3 (m + 19) := by
    exact_mod_cast PA309879.relOS (m + 16)
  have hOS_17 : (PA309879.OS (m + 21) : ℤ) = PA309879.ES (m + 17) + PA309879.N3 (m + 20) := by
    exact_mod_cast PA309879.relOS (m + 17)
  have hOS_18 : (PA309879.OS (m + 22) : ℤ) = PA309879.ES (m + 18) + PA309879.N3 (m + 21) := by
    exact_mod_cast PA309879.relOS (m + 18)
  have hR2_7 : (PA309879.N2 (m + 8) : ℤ) + PA309879.N2 (m + 7) = ((m : ℤ) + 7) + 2 := by
    exact_mod_cast PA309879.relR2 (m + 7)
  have hR2_8 : (PA309879.N2 (m + 9) : ℤ) + PA309879.N2 (m + 8) = ((m : ℤ) + 8) + 2 := by
    exact_mod_cast PA309879.relR2 (m + 8)
  have hR2_9 : (PA309879.N2 (m + 10) : ℤ) + PA309879.N2 (m + 9) = ((m : ℤ) + 9) + 2 := by
    exact_mod_cast PA309879.relR2 (m + 9)
  have hR2_10 : (PA309879.N2 (m + 11) : ℤ) + PA309879.N2 (m + 10) = ((m : ℤ) + 10) + 2 := by
    exact_mod_cast PA309879.relR2 (m + 10)
  have hR2_11 : (PA309879.N2 (m + 12) : ℤ) + PA309879.N2 (m + 11) = ((m : ℤ) + 11) + 2 := by
    exact_mod_cast PA309879.relR2 (m + 11)
  have hR2_12 : (PA309879.N2 (m + 13) : ℤ) + PA309879.N2 (m + 12) = ((m : ℤ) + 12) + 2 := by
    exact_mod_cast PA309879.relR2 (m + 12)
  have hR2_13 : (PA309879.N2 (m + 14) : ℤ) + PA309879.N2 (m + 13) = ((m : ℤ) + 13) + 2 := by
    exact_mod_cast PA309879.relR2 (m + 13)
  have hR2_14 : (PA309879.N2 (m + 15) : ℤ) + PA309879.N2 (m + 14) = ((m : ℤ) + 14) + 2 := by
    exact_mod_cast PA309879.relR2 (m + 14)
  have hR2_15 : (PA309879.N2 (m + 16) : ℤ) + PA309879.N2 (m + 15) = ((m : ℤ) + 15) + 2 := by
    exact_mod_cast PA309879.relR2 (m + 15)
  have hR2_16 : (PA309879.N2 (m + 17) : ℤ) + PA309879.N2 (m + 16) = ((m : ℤ) + 16) + 2 := by
    exact_mod_cast PA309879.relR2 (m + 16)
  have hR2_17 : (PA309879.N2 (m + 18) : ℤ) + PA309879.N2 (m + 17) = ((m : ℤ) + 17) + 2 := by
    exact_mod_cast PA309879.relR2 (m + 17)
  have hR3_7 : (PA309879.N3 (m + 10) : ℤ) = PA309879.N3 (m + 7) + PA309879.N2 (m + 7) := by
    exact_mod_cast PA309879.relR3 (m + 7)
  have hR3_8 : (PA309879.N3 (m + 11) : ℤ) = PA309879.N3 (m + 8) + PA309879.N2 (m + 8) := by
    exact_mod_cast PA309879.relR3 (m + 8)
  have hR3_9 : (PA309879.N3 (m + 12) : ℤ) = PA309879.N3 (m + 9) + PA309879.N2 (m + 9) := by
    exact_mod_cast PA309879.relR3 (m + 9)
  have hR3_16 : (PA309879.N3 (m + 19) : ℤ) = PA309879.N3 (m + 16) + PA309879.N2 (m + 16) := by
    exact_mod_cast PA309879.relR3 (m + 16)
  have hR3_17 : (PA309879.N3 (m + 20) : ℤ) = PA309879.N3 (m + 17) + PA309879.N2 (m + 17) := by
    exact_mod_cast PA309879.relR3 (m + 17)
  have hR3_18 : (PA309879.N3 (m + 21) : ℤ) = PA309879.N3 (m + 18) + PA309879.N2 (m + 18) := by
    exact_mod_cast PA309879.relR3 (m + 18)
  linear_combination ((1 : ℤ)) * hEK_0 + ((-2 : ℤ)) * hEK_1 + ((1 : ℤ)) * hEK_2 + ((-1 : ℤ)) * hEK_3 + ((2 : ℤ))
    * hEK_4 + ((-1 : ℤ)) * hEK_5 + ((-1 : ℤ)) * hEK_8 + ((2 : ℤ)) * hEK_9 + ((-1 : ℤ)) * hEK_10
    + ((1 : ℤ)) * hEK_11 + ((-2 : ℤ)) * hEK_12 + ((1 : ℤ)) * hEK_13 + ((-1 : ℤ)) * hES_8 + ((1 :
    ℤ)) * hES_9 + ((1 : ℤ)) * hES_10 + ((-1 : ℤ)) * hES_12 + ((-1 : ℤ)) * hES_13 + ((1 : ℤ)) *
    hES_14 + ((1 : ℤ)) * hOK_5 + ((-2 : ℤ)) * hOK_6 + ((1 : ℤ)) * hOK_7 + ((-1 : ℤ)) * hOK_8 +
    ((2 : ℤ)) * hOK_9 + ((-1 : ℤ)) * hOK_10 + ((-1 : ℤ)) * hOK_13 + ((2 : ℤ)) * hOK_14 + ((-1 :
    ℤ)) * hOK_15 + ((1 : ℤ)) * hOK_16 + ((-2 : ℤ)) * hOK_17 + ((1 : ℤ)) * hOK_18 + ((-1 : ℤ)) *
    hOS_4 + ((2 : ℤ)) * hOS_5 + ((-1 : ℤ)) * hOS_6 + ((1 : ℤ)) * hOS_7 + ((-2 : ℤ)) * hOS_8 +
    ((1 : ℤ)) * hOS_9 + ((-1 : ℤ)) * hOS_13 + ((2 : ℤ)) * hOS_14 + ((-1 : ℤ)) * hOS_15 + ((1 :
    ℤ)) * hOS_16 + ((-2 : ℤ)) * hOS_17 + ((1 : ℤ)) * hOS_18 + ((1 : ℤ)) * hR2_7 + ((-3 : ℤ)) *
    hR2_8 + ((4 : ℤ)) * hR2_9 + ((-4 : ℤ)) * hR2_10 + ((4 : ℤ)) * hR2_11 + ((-4 : ℤ)) * hR2_12 +
    ((4 : ℤ)) * hR2_13 + ((-4 : ℤ)) * hR2_14 + ((4 : ℤ)) * hR2_15 + ((-3 : ℤ)) * hR2_16 + ((1 :
    ℤ)) * hR2_17 + ((1 : ℤ)) * hR3_7 + ((-2 : ℤ)) * hR3_8 + ((1 : ℤ)) * hR3_9 + ((1 : ℤ)) *
    hR3_16 + ((-2 : ℤ)) * hR3_17 + ((1 : ℤ)) * hR3_18
