import OMAStatements.S_oeis_a308824
import Mathlib

/-!
# A308824: Barker's recurrence

Adding 1 to every part maps the partitions of m into 5 parts onto those of m + 5 with smallest part
at least 2; the partitions with smallest part 1 are 1 + (a partition of m + 4 into 4 parts), whose
second smallest part is the smallest part of that partition. With N5, N4, N3 the numbers of
partitions into 5, 4, 3 parts, T5 the sum of the second smallest parts and S4 the sum of the
smallest parts of the partitions into 4 parts:
T5(m + 5) = T5(m) + N5(m) + S4(m + 4), S4(r + 4) = S4(r) + N4(r) + N3(r + 3),
N5(m + 5) = N5(m) + N4(m + 4), N4(r + 4) = N4(r) + N3(r + 3), N3(r + 3) = N3(r) + N2(r) and
N2(r + 1) + N2(r) = r + 2 with N2(r) = floor((r + 2)/2).
Barker's operator applied to T5 is an explicit integer combination of these relations.
-/

namespace PA308824

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

def T5 (m : ℕ) : ℕ := H5 (fun _ k _ _ _ => k) m

def S4 (r : ℕ) : ℕ := H4L (fun k _ _ _ => k) r 1

theorem relT5 (m : ℕ) : T5 (m + 5) = T5 m + N5 m + S4 (m + 4) := by
  unfold T5 N5 S4
  rw [H5_shift, H5_add (fun _ k _ _ _ => k) (fun _ _ _ _ _ => 1)]

theorem relS4 (r : ℕ) : S4 (r + 4) = S4 r + N4 r + N3 (r + 3) := by
  unfold S4 N4 N3
  rw [H4L_peel, H4L_add (fun k _ _ _ => k) (fun _ _ _ _ => 1)]

theorem a_eq (n : ℕ) : OMA.S_oeis_a308824.a n = T5 n := by
  unfold OMA.S_oeis_a308824.a T5 H5
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

end PA308824

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a308824.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 21 := ⟨n - 21, by omega⟩
  simp only [show m + 21 - 1 = m + 20 by omega, show m + 21 - 2 = m + 19 by omega, show m + 21 - 3 = m +
    18 by omega, show m + 21 - 4 = m + 17 by omega, show m + 21 - 6 = m + 15 by omega, show m +
    21 - 8 = m + 13 by omega, show m + 21 - 9 = m + 12 by omega, show m + 21 - 10 = m + 11 by
    omega, show m + 21 - 11 = m + 10 by omega, show m + 21 - 12 = m + 9 by omega, show m + 21 -
    13 = m + 8 by omega, show m + 21 - 15 = m + 6 by omega, show m + 21 - 17 = m + 4 by omega,
    show m + 21 - 18 = m + 3 by omega, show m + 21 - 19 = m + 2 by omega, show m + 21 - 20 = m +
    1 by omega, show m + 21 - 21 = m by omega, PA308824.a_eq]
  have hR2_7 : (PA308824.N2 (m + 8) : ℤ) + PA308824.N2 (m + 7) = ((m : ℤ) + 7) + 2 := by
    exact_mod_cast PA308824.relR2 (m + 7)
  have hR2_8 : (PA308824.N2 (m + 9) : ℤ) + PA308824.N2 (m + 8) = ((m : ℤ) + 8) + 2 := by
    exact_mod_cast PA308824.relR2 (m + 8)
  have hR2_9 : (PA308824.N2 (m + 10) : ℤ) + PA308824.N2 (m + 9) = ((m : ℤ) + 9) + 2 := by
    exact_mod_cast PA308824.relR2 (m + 9)
  have hR2_10 : (PA308824.N2 (m + 11) : ℤ) + PA308824.N2 (m + 10) = ((m : ℤ) + 10) + 2 := by
    exact_mod_cast PA308824.relR2 (m + 10)
  have hR2_11 : (PA308824.N2 (m + 12) : ℤ) + PA308824.N2 (m + 11) = ((m : ℤ) + 11) + 2 := by
    exact_mod_cast PA308824.relR2 (m + 11)
  have hR2_12 : (PA308824.N2 (m + 13) : ℤ) + PA308824.N2 (m + 12) = ((m : ℤ) + 12) + 2 := by
    exact_mod_cast PA308824.relR2 (m + 12)
  have hR2_13 : (PA308824.N2 (m + 14) : ℤ) + PA308824.N2 (m + 13) = ((m : ℤ) + 13) + 2 := by
    exact_mod_cast PA308824.relR2 (m + 13)
  have hR2_14 : (PA308824.N2 (m + 15) : ℤ) + PA308824.N2 (m + 14) = ((m : ℤ) + 14) + 2 := by
    exact_mod_cast PA308824.relR2 (m + 14)
  have hR2_15 : (PA308824.N2 (m + 16) : ℤ) + PA308824.N2 (m + 15) = ((m : ℤ) + 15) + 2 := by
    exact_mod_cast PA308824.relR2 (m + 15)
  have hR3_7 : (PA308824.N3 (m + 10) : ℤ) = PA308824.N3 (m + 7) + PA308824.N2 (m + 7) := by
    exact_mod_cast PA308824.relR3 (m + 7)
  have hR3_8 : (PA308824.N3 (m + 11) : ℤ) = PA308824.N3 (m + 8) + PA308824.N2 (m + 8) := by
    exact_mod_cast PA308824.relR3 (m + 8)
  have hR3_9 : (PA308824.N3 (m + 12) : ℤ) = PA308824.N3 (m + 9) + PA308824.N2 (m + 9) := by
    exact_mod_cast PA308824.relR3 (m + 9)
  have hR3_10 : (PA308824.N3 (m + 13) : ℤ) = PA308824.N3 (m + 10) + PA308824.N2 (m + 10) := by
    exact_mod_cast PA308824.relR3 (m + 10)
  have hR3_11 : (PA308824.N3 (m + 14) : ℤ) = PA308824.N3 (m + 11) + PA308824.N2 (m + 11) := by
    exact_mod_cast PA308824.relR3 (m + 11)
  have hR3_12 : (PA308824.N3 (m + 15) : ℤ) = PA308824.N3 (m + 12) + PA308824.N2 (m + 12) := by
    exact_mod_cast PA308824.relR3 (m + 12)
  have hR3_13 : (PA308824.N3 (m + 16) : ℤ) = PA308824.N3 (m + 13) + PA308824.N2 (m + 13) := by
    exact_mod_cast PA308824.relR3 (m + 13)
  have hR3_14 : (PA308824.N3 (m + 17) : ℤ) = PA308824.N3 (m + 14) + PA308824.N2 (m + 14) := by
    exact_mod_cast PA308824.relR3 (m + 14)
  have hR3_15 : (PA308824.N3 (m + 18) : ℤ) = PA308824.N3 (m + 15) + PA308824.N2 (m + 15) := by
    exact_mod_cast PA308824.relR3 (m + 15)
  have hR3_16 : (PA308824.N3 (m + 19) : ℤ) = PA308824.N3 (m + 16) + PA308824.N2 (m + 16) := by
    exact_mod_cast PA308824.relR3 (m + 16)
  have hR4_4 : (PA308824.N4 (m + 8) : ℤ) = PA308824.N4 (m + 4) + PA308824.N3 (m + 7) := by
    exact_mod_cast PA308824.relR4 (m + 4)
  have hR4_5 : (PA308824.N4 (m + 9) : ℤ) = PA308824.N4 (m + 5) + PA308824.N3 (m + 8) := by
    exact_mod_cast PA308824.relR4 (m + 5)
  have hR4_6 : (PA308824.N4 (m + 10) : ℤ) = PA308824.N4 (m + 6) + PA308824.N3 (m + 9) := by
    exact_mod_cast PA308824.relR4 (m + 6)
  have hR4_7 : (PA308824.N4 (m + 11) : ℤ) = PA308824.N4 (m + 7) + PA308824.N3 (m + 10) := by
    exact_mod_cast PA308824.relR4 (m + 7)
  have hR4_8 : (PA308824.N4 (m + 12) : ℤ) = PA308824.N4 (m + 8) + PA308824.N3 (m + 11) := by
    exact_mod_cast PA308824.relR4 (m + 8)
  have hR4_10 : (PA308824.N4 (m + 14) : ℤ) = PA308824.N4 (m + 10) + PA308824.N3 (m + 13) := by
    exact_mod_cast PA308824.relR4 (m + 10)
  have hR4_12 : (PA308824.N4 (m + 16) : ℤ) = PA308824.N4 (m + 12) + PA308824.N3 (m + 15) := by
    exact_mod_cast PA308824.relR4 (m + 12)
  have hR5_0 : (PA308824.N5 (m + 5) : ℤ) = PA308824.N5 (m) + PA308824.N4 (m + 4) := by
    exact_mod_cast PA308824.relR5 (m)
  have hR5_1 : (PA308824.N5 (m + 6) : ℤ) = PA308824.N5 (m + 1) + PA308824.N4 (m + 5) := by
    exact_mod_cast PA308824.relR5 (m + 1)
  have hR5_2 : (PA308824.N5 (m + 7) : ℤ) = PA308824.N5 (m + 2) + PA308824.N4 (m + 6) := by
    exact_mod_cast PA308824.relR5 (m + 2)
  have hR5_3 : (PA308824.N5 (m + 8) : ℤ) = PA308824.N5 (m + 3) + PA308824.N4 (m + 7) := by
    exact_mod_cast PA308824.relR5 (m + 3)
  have hR5_4 : (PA308824.N5 (m + 9) : ℤ) = PA308824.N5 (m + 4) + PA308824.N4 (m + 8) := by
    exact_mod_cast PA308824.relR5 (m + 4)
  have hR5_5 : (PA308824.N5 (m + 10) : ℤ) = PA308824.N5 (m + 5) + PA308824.N4 (m + 9) := by
    exact_mod_cast PA308824.relR5 (m + 5)
  have hR5_6 : (PA308824.N5 (m + 11) : ℤ) = PA308824.N5 (m + 6) + PA308824.N4 (m + 10) := by
    exact_mod_cast PA308824.relR5 (m + 6)
  have hR5_7 : (PA308824.N5 (m + 12) : ℤ) = PA308824.N5 (m + 7) + PA308824.N4 (m + 11) := by
    exact_mod_cast PA308824.relR5 (m + 7)
  have hR5_8 : (PA308824.N5 (m + 13) : ℤ) = PA308824.N5 (m + 8) + PA308824.N4 (m + 12) := by
    exact_mod_cast PA308824.relR5 (m + 8)
  have hR5_9 : (PA308824.N5 (m + 14) : ℤ) = PA308824.N5 (m + 9) + PA308824.N4 (m + 13) := by
    exact_mod_cast PA308824.relR5 (m + 9)
  have hR5_10 : (PA308824.N5 (m + 15) : ℤ) = PA308824.N5 (m + 10) + PA308824.N4 (m + 14) := by
    exact_mod_cast PA308824.relR5 (m + 10)
  have hR5_11 : (PA308824.N5 (m + 16) : ℤ) = PA308824.N5 (m + 11) + PA308824.N4 (m + 15) := by
    exact_mod_cast PA308824.relR5 (m + 11)
  have hS4_4 : (PA308824.S4 (m + 8) : ℤ) = PA308824.S4 (m + 4) + PA308824.N4 (m + 4) + PA308824.N3 (m + 7) := by
    exact_mod_cast PA308824.relS4 (m + 4)
  have hS4_5 : (PA308824.S4 (m + 9) : ℤ) = PA308824.S4 (m + 5) + PA308824.N4 (m + 5) + PA308824.N3 (m + 8) := by
    exact_mod_cast PA308824.relS4 (m + 5)
  have hS4_6 : (PA308824.S4 (m + 10) : ℤ) = PA308824.S4 (m + 6) + PA308824.N4 (m + 6) + PA308824.N3 (m + 9) := by
    exact_mod_cast PA308824.relS4 (m + 6)
  have hS4_7 : (PA308824.S4 (m + 11) : ℤ) = PA308824.S4 (m + 7) + PA308824.N4 (m + 7) + PA308824.N3 (m + 10) := by
    exact_mod_cast PA308824.relS4 (m + 7)
  have hS4_8 : (PA308824.S4 (m + 12) : ℤ) = PA308824.S4 (m + 8) + PA308824.N4 (m + 8) + PA308824.N3 (m + 11) := by
    exact_mod_cast PA308824.relS4 (m + 8)
  have hS4_10 : (PA308824.S4 (m + 14) : ℤ) = PA308824.S4 (m + 10) + PA308824.N4 (m + 10) + PA308824.N3 (m + 13) := by
    exact_mod_cast PA308824.relS4 (m + 10)
  have hS4_12 : (PA308824.S4 (m + 16) : ℤ) = PA308824.S4 (m + 12) + PA308824.N4 (m + 12) + PA308824.N3 (m + 15) := by
    exact_mod_cast PA308824.relS4 (m + 12)
  have hS4_13 : (PA308824.S4 (m + 17) : ℤ) = PA308824.S4 (m + 13) + PA308824.N4 (m + 13) + PA308824.N3 (m + 16) := by
    exact_mod_cast PA308824.relS4 (m + 13)
  have hS4_14 : (PA308824.S4 (m + 18) : ℤ) = PA308824.S4 (m + 14) + PA308824.N4 (m + 14) + PA308824.N3 (m + 17) := by
    exact_mod_cast PA308824.relS4 (m + 14)
  have hS4_15 : (PA308824.S4 (m + 19) : ℤ) = PA308824.S4 (m + 15) + PA308824.N4 (m + 15) + PA308824.N3 (m + 18) := by
    exact_mod_cast PA308824.relS4 (m + 15)
  have hS4_16 : (PA308824.S4 (m + 20) : ℤ) = PA308824.S4 (m + 16) + PA308824.N4 (m + 16) + PA308824.N3 (m + 19) := by
    exact_mod_cast PA308824.relS4 (m + 16)
  have hT5_0 : (PA308824.T5 (m + 5) : ℤ) = PA308824.T5 (m) + PA308824.N5 (m) + PA308824.S4 (m + 4) := by
    exact_mod_cast PA308824.relT5 (m)
  have hT5_1 : (PA308824.T5 (m + 6) : ℤ) = PA308824.T5 (m + 1) + PA308824.N5 (m + 1) + PA308824.S4 (m + 5) := by
    exact_mod_cast PA308824.relT5 (m + 1)
  have hT5_2 : (PA308824.T5 (m + 7) : ℤ) = PA308824.T5 (m + 2) + PA308824.N5 (m + 2) + PA308824.S4 (m + 6) := by
    exact_mod_cast PA308824.relT5 (m + 2)
  have hT5_3 : (PA308824.T5 (m + 8) : ℤ) = PA308824.T5 (m + 3) + PA308824.N5 (m + 3) + PA308824.S4 (m + 7) := by
    exact_mod_cast PA308824.relT5 (m + 3)
  have hT5_4 : (PA308824.T5 (m + 9) : ℤ) = PA308824.T5 (m + 4) + PA308824.N5 (m + 4) + PA308824.S4 (m + 8) := by
    exact_mod_cast PA308824.relT5 (m + 4)
  have hT5_5 : (PA308824.T5 (m + 10) : ℤ) = PA308824.T5 (m + 5) + PA308824.N5 (m + 5) + PA308824.S4 (m + 9) := by
    exact_mod_cast PA308824.relT5 (m + 5)
  have hT5_6 : (PA308824.T5 (m + 11) : ℤ) = PA308824.T5 (m + 6) + PA308824.N5 (m + 6) + PA308824.S4 (m + 10) := by
    exact_mod_cast PA308824.relT5 (m + 6)
  have hT5_7 : (PA308824.T5 (m + 12) : ℤ) = PA308824.T5 (m + 7) + PA308824.N5 (m + 7) + PA308824.S4 (m + 11) := by
    exact_mod_cast PA308824.relT5 (m + 7)
  have hT5_9 : (PA308824.T5 (m + 14) : ℤ) = PA308824.T5 (m + 9) + PA308824.N5 (m + 9) + PA308824.S4 (m + 13) := by
    exact_mod_cast PA308824.relT5 (m + 9)
  have hT5_10 : (PA308824.T5 (m + 15) : ℤ) = PA308824.T5 (m + 10) + PA308824.N5 (m + 10) + PA308824.S4 (m + 14) := by
    exact_mod_cast PA308824.relT5 (m + 10)
  have hT5_11 : (PA308824.T5 (m + 16) : ℤ) = PA308824.T5 (m + 11) + PA308824.N5 (m + 11) + PA308824.S4 (m + 15) := by
    exact_mod_cast PA308824.relT5 (m + 11)
  have hT5_12 : (PA308824.T5 (m + 17) : ℤ) = PA308824.T5 (m + 12) + PA308824.N5 (m + 12) + PA308824.S4 (m + 16) := by
    exact_mod_cast PA308824.relT5 (m + 12)
  have hT5_13 : (PA308824.T5 (m + 18) : ℤ) = PA308824.T5 (m + 13) + PA308824.N5 (m + 13) + PA308824.S4 (m + 17) := by
    exact_mod_cast PA308824.relT5 (m + 13)
  have hT5_14 : (PA308824.T5 (m + 19) : ℤ) = PA308824.T5 (m + 14) + PA308824.N5 (m + 14) + PA308824.S4 (m + 18) := by
    exact_mod_cast PA308824.relT5 (m + 14)
  have hT5_15 : (PA308824.T5 (m + 20) : ℤ) = PA308824.T5 (m + 15) + PA308824.N5 (m + 15) + PA308824.S4 (m + 19) := by
    exact_mod_cast PA308824.relT5 (m + 15)
  have hT5_16 : (PA308824.T5 (m + 21) : ℤ) = PA308824.T5 (m + 16) + PA308824.N5 (m + 16) + PA308824.S4 (m + 20) := by
    exact_mod_cast PA308824.relT5 (m + 16)
  linear_combination ((1 : ℤ)) * hR2_7 + ((-2 : ℤ)) * hR2_8 + ((1 : ℤ)) * hR2_9 + ((1 : ℤ)) * hR2_10 + ((-2 : ℤ))
    * hR2_11 + ((1 : ℤ)) * hR2_12 + ((1 : ℤ)) * hR2_13 + ((-2 : ℤ)) * hR2_14 + ((1 : ℤ)) *
    hR2_15 + ((1 : ℤ)) * hR3_7 + ((-1 : ℤ)) * hR3_8 + ((-1 : ℤ)) * hR3_9 + ((2 : ℤ)) * hR3_10 +
    ((-1 : ℤ)) * hR3_11 + ((-1 : ℤ)) * hR3_12 + ((2 : ℤ)) * hR3_13 + ((-1 : ℤ)) * hR3_14 + ((-1
    : ℤ)) * hR3_15 + ((1 : ℤ)) * hR3_16 + ((-2 : ℤ)) * hR4_4 + ((2 : ℤ)) * hR4_5 + ((2 : ℤ)) *
    hR4_6 + ((-2 : ℤ)) * hR4_7 + ((1 : ℤ)) * hR4_8 + ((-2 : ℤ)) * hR4_10 + ((1 : ℤ)) * hR4_12 +
    ((1 : ℤ)) * hR5_0 + ((-1 : ℤ)) * hR5_1 + ((-1 : ℤ)) * hR5_2 + ((1 : ℤ)) * hR5_3 + ((-2 : ℤ))
    * hR5_4 + ((2 : ℤ)) * hR5_5 + ((2 : ℤ)) * hR5_6 + ((-2 : ℤ)) * hR5_7 + ((1 : ℤ)) * hR5_8 +
    ((-1 : ℤ)) * hR5_9 + ((-1 : ℤ)) * hR5_10 + ((1 : ℤ)) * hR5_11 + ((1 : ℤ)) * hS4_4 + ((-1 :
    ℤ)) * hS4_5 + ((-1 : ℤ)) * hS4_6 + ((1 : ℤ)) * hS4_7 + ((-1 : ℤ)) * hS4_8 + ((2 : ℤ)) *
    hS4_10 + ((-1 : ℤ)) * hS4_12 + ((1 : ℤ)) * hS4_13 + ((-1 : ℤ)) * hS4_14 + ((-1 : ℤ)) *
    hS4_15 + ((1 : ℤ)) * hS4_16 + ((-1 : ℤ)) * hT5_0 + ((1 : ℤ)) * hT5_1 + ((1 : ℤ)) * hT5_2 +
    ((-1 : ℤ)) * hT5_3 + ((2 : ℤ)) * hT5_4 + ((-1 : ℤ)) * hT5_5 + ((-3 : ℤ)) * hT5_6 + ((1 : ℤ))
    * hT5_7 + ((-1 : ℤ)) * hT5_9 + ((3 : ℤ)) * hT5_10 + ((1 : ℤ)) * hT5_11 + ((-2 : ℤ)) * hT5_12
    + ((1 : ℤ)) * hT5_13 + ((-1 : ℤ)) * hT5_14 + ((-1 : ℤ)) * hT5_15 + ((1 : ℤ)) * hT5_16
