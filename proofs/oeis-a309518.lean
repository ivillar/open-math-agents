import OMAStatements.S_oeis_a309518
import Mathlib

/-!
# A309518: Barker's recurrence

Write a partition of m into 4 parts as k + j + i + c with k <= j <= i <= c. Adding 1 to every
part maps the partitions of m onto those of m + 4 with smallest part at least 2 and swaps odd and
even parts; the partitions with smallest part 1 are 1 + (a partition of m + 3 into 3 parts). With
O4, E4 (resp. O3, E3) the numbers of odd and even parts over the partitions into 4 (resp. 3)
parts, N3 the number of partitions into 3 parts, and GO(t), GE(t) the numbers of odd and even
parts over the partitions (1, b, c) of t:
O4(m + 4) = E4(m) + N3(m + 3) + O3(m + 3), E4(m + 4) = O4(m) + E3(m + 3),
O3(r + 3) = E3(r) + GO(r + 3), E3(r + 3) = O3(r) + GE(r + 3), N3(r + 3) = N3(r) + N2(r).
The slice counts satisfy GO(t + 2) + GO(t) + 2 = 2t + 3 (t mod 2), GE(t + 2) + GE(t) + 1 = t and
2 GO(t) + 2 GE(t) + 3 ((t + 1) mod 2) + 3 = 3t for t >= 1 (each proved by a two-step induction or
by counting 3 parts per partition), and N2(r) = floor((r + 2)/2) satisfies N2(r + 1) + N2(r) = r + 2.
Barker's operator applied to the sequence is an explicit integer combination of these relations.
-/

namespace PA309518

theorem icc_range (m : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 m, f k = ∑ t ∈ Finset.range m, f (t + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem icc_range' (k X : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc k X, f i = ∑ j ∈ Finset.range (X + 1 - k), f (k + j) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]

/-- Number of odd values among `x, y, z`. -/
def wo (x y z : ℕ) : ℕ := x % 2 + y % 2 + z % 2

/-- Number of even values among `x, y, z`. -/
def we (x y z : ℕ) : ℕ := (x + 1) % 2 + (y + 1) % 2 + (z + 1) % 2

/-- Weighted sum over the partitions `j + i + (r - i - j)` of `r` with fixed smallest part `j`. -/
def I3 (w : ℕ → ℕ → ℕ → ℕ) (r j : ℕ) : ℕ :=
  ∑ u ∈ Finset.range ((r - j) / 2 + 1 - j), w j (j + u) (r - (j + u) - j)

/-- Weighted sum over the partitions of `r` into 3 parts, all at least `k`. -/
def H3 (w : ℕ → ℕ → ℕ → ℕ) (r k : ℕ) : ℕ :=
  ∑ s ∈ Finset.range (r / 3 + 1 - k), I3 w r (k + s)

/-- Weighted sum over the partitions of `m` into 4 parts (the weight sees the smallest part). -/
def H4 (W : ℕ → ℕ → ℕ → ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (m / 4), H3 (W (t + 1)) (m - (t + 1)) (t + 1)

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

theorem H4_shift (W : ℕ → ℕ → ℕ → ℕ → ℕ) (m : ℕ) :
    H4 W (m + 4) = H4 (fun k x y z => W (k + 1) (x + 1) (y + 1) (z + 1)) m +
      H3 (W 1) (m + 3) 1 := by
  unfold H4
  rw [show (m + 4) / 4 = m / 4 + 1 by omega, Finset.sum_range_succ',
    show m + 4 - (0 + 1) = m + 3 by omega]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [show m + 4 - (t + 1 + 1) = m - (t + 1) + 3 by omega]
  exact H3_shift (W (t + 1 + 1)) (m - (t + 1)) (t + 1)

theorem H3_congr (w w' : ℕ → ℕ → ℕ → ℕ) (r k : ℕ) (h : ∀ x y z, w x y z = w' x y z) :
    H3 w r k = H3 w' r k := by
  rw [show w = w' from funext fun x => funext fun y => funext fun z => h x y z]

theorem H4_congr (W W' : ℕ → ℕ → ℕ → ℕ → ℕ) (m : ℕ)
    (h : ∀ k x y z, W k x y z = W' k x y z) : H4 W m = H4 W' m := by
  rw [show W = W' from funext fun k => funext fun x => funext fun y => funext fun z => h k x y z]

theorem H3_add (f g : ℕ → ℕ → ℕ → ℕ) (r k : ℕ) :
    H3 (fun x y z => f x y z + g x y z) r k = H3 f r k + H3 g r k := by
  unfold H3 I3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]

def W4o (k x y z : ℕ) : ℕ := k % 2 + wo x y z

def W4e (k x y z : ℕ) : ℕ := (k + 1) % 2 + we x y z

def O4 (m : ℕ) : ℕ := H4 W4o m

def E4 (m : ℕ) : ℕ := H4 W4e m

def O3 (r : ℕ) : ℕ := H3 wo r 1

def E3 (r : ℕ) : ℕ := H3 we r 1

def N3 (r : ℕ) : ℕ := H3 (fun _ _ _ => 1) r 1

def GO (t : ℕ) : ℕ := I3 wo t 1

def GE (t : ℕ) : ℕ := I3 we t 1

def N2 (r : ℕ) : ℕ := (r + 2) / 2

def Par (t : ℕ) : ℕ := t % 2

/-- The term added to `GO t` when passing to `GO (t + 2)`. -/
def dO (t : ℕ) : ℕ := wo 1 (1 + (t - 1) / 2) (t - (t - 1) / 2)

/-- The term added to `GE t` when passing to `GE (t + 2)`. -/
def dE (t : ℕ) : ℕ := we 1 (1 + (t - 1) / 2) (t - (t - 1) / 2)

theorem relA (m : ℕ) : O4 (m + 4) = E4 m + N3 (m + 3) + O3 (m + 3) := by
  unfold O4 E4 N3 O3
  rw [H4_shift, H4_congr _ W4e m (fun k x y z => by unfold W4o W4e wo we; omega),
    H3_congr (W4o 1) (fun x y z => 1 + wo x y z) _ _ (fun x y z => by unfold W4o; omega),
    H3_add, add_assoc]

theorem relB (m : ℕ) : E4 (m + 4) = O4 m + E3 (m + 3) := by
  unfold O4 E4 E3
  rw [H4_shift, H4_congr _ W4o m (fun k x y z => by unfold W4o W4e wo we; omega),
    H3_congr (W4e 1) we _ _ (fun x y z => by unfold W4e; omega)]

theorem relC (r : ℕ) : O3 (r + 3) = E3 r + GO (r + 3) := by
  unfold O3 E3 GO
  rw [H3_peel, H3_congr _ we r 1 (fun x y z => by unfold wo we; omega)]

theorem relD (r : ℕ) : E3 (r + 3) = O3 r + GE (r + 3) := by
  unfold O3 E3 GE
  rw [H3_peel, H3_congr _ wo r 1 (fun x y z => by unfold wo we; omega)]

theorem relR3 (r : ℕ) : N3 (r + 3) = N3 r + N2 r := by
  unfold N3 N2
  rw [H3_peel]
  congr 1
  unfold I3
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  omega

theorem GO_step (t : ℕ) (ht : 1 ≤ t) : GO (t + 2) = GO t + dO t := by
  unfold GO I3 dO
  rw [show (t + 2 - 1) / 2 + 1 - 1 = (t - 1) / 2 + 1 by omega,
    show (t - 1) / 2 + 1 - 1 = (t - 1) / 2 by omega, Finset.sum_range_succ,
    show t + 2 - (1 + (t - 1) / 2) - 1 = t - (t - 1) / 2 by omega]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_range] at hu
  unfold wo
  omega

theorem GE_step (t : ℕ) (ht : 1 ≤ t) : GE (t + 2) = GE t + dE t := by
  unfold GE I3 dE
  rw [show (t + 2 - 1) / 2 + 1 - 1 = (t - 1) / 2 + 1 by omega,
    show (t - 1) / 2 + 1 - 1 = (t - 1) / 2 by omega, Finset.sum_range_succ,
    show t + 2 - (1 + (t - 1) / 2) - 1 = t - (t - 1) / 2 by omega]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_range] at hu
  unfold we
  omega

theorem dO_sum (t : ℕ) (ht : 1 ≤ t) : dO t + dO (t + 2) = 4 := by
  unfold dO wo
  omega

theorem dE_sum (t : ℕ) (ht : 1 ≤ t) : dE t + dE (t + 2) = 2 := by
  unfold dE we
  omega

theorem GO_one : GO 1 = 0 := rfl

theorem GO_two : GO 2 = 0 := rfl

theorem GE_one : GE 1 = 0 := rfl

theorem GE_two : GE 2 = 0 := rfl

theorem PO_aux (r : ℕ) : 2 * GO (r + 1) + dO (r + 1) = 2 * r + 3 * ((r + 1) % 2) ∧
    2 * GO (r + 2) + dO (r + 2) = 2 * (r + 1) + 3 * ((r + 2) % 2) := by
  induction r with
  | zero =>
    rw [GO_one, GO_two]
    unfold dO wo
    omega
  | succ r ih =>
    refine ⟨ih.2, ?_⟩
    rw [GO_step (r + 1) (by omega)]
    have h1 := ih.1
    have h2 := dO_sum (r + 1) (by omega)
    omega

theorem PE_aux (r : ℕ) : 2 * GE (r + 1) + dE (r + 1) = r ∧
    2 * GE (r + 2) + dE (r + 2) = r + 1 := by
  induction r with
  | zero =>
    rw [GE_one, GE_two]
    unfold dE we
    omega
  | succ r ih =>
    refine ⟨ih.2, ?_⟩
    rw [GE_step (r + 1) (by omega)]
    have h1 := ih.1
    have h2 := dE_sum (r + 1) (by omega)
    omega

theorem relG (t : ℕ) (ht : 1 ≤ t) : GO (t + 2) + GO t + 2 = 2 * t + 3 * Par t := by
  obtain ⟨r, rfl⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
  rw [GO_step _ ht]
  have h := (PO_aux r).1
  unfold Par
  omega

theorem relH (t : ℕ) (ht : 1 ≤ t) : GE (t + 2) + GE t + 1 = t := by
  obtain ⟨r, rfl⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
  rw [GE_step _ ht]
  have h := (PE_aux r).1
  omega

theorem relS (t : ℕ) : GO t + GE t = 3 * ((t - 1) / 2 + 1 - 1) := by
  unfold GO GE I3
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (g := fun _ => 3)
    (fun u _ => by unfold wo we; omega), Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_comm]

theorem relS2 (t : ℕ) (ht : 1 ≤ t) : 2 * GO t + 2 * GE t + 3 * Par (t + 1) + 3 = 3 * t := by
  have h := relS t
  unfold Par
  omega

theorem relP2 (t : ℕ) : Par (t + 2) = Par t := by
  unfold Par
  omega

theorem relP1 (t : ℕ) : Par (t + 1) + Par t = 1 := by
  unfold Par
  omega

theorem relR2 (t : ℕ) : N2 (t + 1) + N2 t = t + 2 := by
  unfold N2
  omega

theorem relN2p (t : ℕ) : 2 * N2 t + Par t = t + 2 := by
  unfold N2 Par
  omega

theorem a_eq (n : ℕ) : OMA.S_oeis_a309518.a n = E4 n := by
  unfold OMA.S_oeis_a309518.a E4 H4
  rw [icc_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold H3
  rw [icc_range']
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold I3
  rw [icc_range', show (n - (t + 1 + s) - (t + 1)) / 2 + 1 - (t + 1 + s) =
    (n - (t + 1) - (t + 1 + s)) / 2 + 1 - (t + 1 + s) by omega]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_range] at hu
  unfold W4e we
  omega

end PA309518

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a309518.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 15 := ⟨n - 15, by omega⟩
  simp only [show m + 15 - 1 = m + 14 by omega, show m + 15 - 2 = m + 13 by omega, show m + 15 - 3 = m +
    12 by omega, show m + 15 - 4 = m + 11 by omega, show m + 15 - 5 = m + 10 by omega, show m +
    15 - 6 = m + 9 by omega, show m + 15 - 7 = m + 8 by omega, show m + 15 - 8 = m + 7 by omega,
    show m + 15 - 9 = m + 6 by omega, show m + 15 - 10 = m + 5 by omega, show m + 15 - 11 = m +
    4 by omega, show m + 15 - 12 = m + 3 by omega, show m + 15 - 13 = m + 2 by omega, show m +
    15 - 14 = m + 1 by omega, show m + 15 - 15 = m by omega, PA309518.a_eq]
  have hA_0 : (PA309518.O4 (m + 4) : ℤ) = PA309518.E4 (m) + PA309518.N3 (m + 3) + PA309518.O3 (m + 3) := by
    exact_mod_cast PA309518.relA (m)
  have hA_1 : (PA309518.O4 (m + 5) : ℤ) = PA309518.E4 (m + 1) + PA309518.N3 (m + 4) + PA309518.O3 (m + 4) := by
    exact_mod_cast PA309518.relA (m + 1)
  have hA_2 : (PA309518.O4 (m + 6) : ℤ) = PA309518.E4 (m + 2) + PA309518.N3 (m + 5) + PA309518.O3 (m + 5) := by
    exact_mod_cast PA309518.relA (m + 2)
  have hA_3 : (PA309518.O4 (m + 7) : ℤ) = PA309518.E4 (m + 3) + PA309518.N3 (m + 6) + PA309518.O3 (m + 6) := by
    exact_mod_cast PA309518.relA (m + 3)
  have hA_4 : (PA309518.O4 (m + 8) : ℤ) = PA309518.E4 (m + 4) + PA309518.N3 (m + 7) + PA309518.O3 (m + 7) := by
    exact_mod_cast PA309518.relA (m + 4)
  have hA_5 : (PA309518.O4 (m + 9) : ℤ) = PA309518.E4 (m + 5) + PA309518.N3 (m + 8) + PA309518.O3 (m + 8) := by
    exact_mod_cast PA309518.relA (m + 5)
  have hA_6 : (PA309518.O4 (m + 10) : ℤ) = PA309518.E4 (m + 6) + PA309518.N3 (m + 9) + PA309518.O3 (m + 9) := by
    exact_mod_cast PA309518.relA (m + 6)
  have hA_7 : (PA309518.O4 (m + 11) : ℤ) = PA309518.E4 (m + 7) + PA309518.N3 (m + 10) + PA309518.O3 (m + 10) := by
    exact_mod_cast PA309518.relA (m + 7)
  have hB_4 : (PA309518.E4 (m + 8) : ℤ) = PA309518.O4 (m + 4) + PA309518.E3 (m + 7) := by
    exact_mod_cast PA309518.relB (m + 4)
  have hB_5 : (PA309518.E4 (m + 9) : ℤ) = PA309518.O4 (m + 5) + PA309518.E3 (m + 8) := by
    exact_mod_cast PA309518.relB (m + 5)
  have hB_6 : (PA309518.E4 (m + 10) : ℤ) = PA309518.O4 (m + 6) + PA309518.E3 (m + 9) := by
    exact_mod_cast PA309518.relB (m + 6)
  have hB_7 : (PA309518.E4 (m + 11) : ℤ) = PA309518.O4 (m + 7) + PA309518.E3 (m + 10) := by
    exact_mod_cast PA309518.relB (m + 7)
  have hB_8 : (PA309518.E4 (m + 12) : ℤ) = PA309518.O4 (m + 8) + PA309518.E3 (m + 11) := by
    exact_mod_cast PA309518.relB (m + 8)
  have hB_9 : (PA309518.E4 (m + 13) : ℤ) = PA309518.O4 (m + 9) + PA309518.E3 (m + 12) := by
    exact_mod_cast PA309518.relB (m + 9)
  have hB_10 : (PA309518.E4 (m + 14) : ℤ) = PA309518.O4 (m + 10) + PA309518.E3 (m + 13) := by
    exact_mod_cast PA309518.relB (m + 10)
  have hB_11 : (PA309518.E4 (m + 15) : ℤ) = PA309518.O4 (m + 11) + PA309518.E3 (m + 14) := by
    exact_mod_cast PA309518.relB (m + 11)
  have hC_6 : (PA309518.O3 (m + 9) : ℤ) = PA309518.E3 (m + 6) + PA309518.GO (m + 9) := by
    exact_mod_cast PA309518.relC (m + 6)
  have hC_7 : (PA309518.O3 (m + 10) : ℤ) = PA309518.E3 (m + 7) + PA309518.GO (m + 10) := by
    exact_mod_cast PA309518.relC (m + 7)
  have hC_8 : (PA309518.O3 (m + 11) : ℤ) = PA309518.E3 (m + 8) + PA309518.GO (m + 11) := by
    exact_mod_cast PA309518.relC (m + 8)
  have hD_3 : (PA309518.E3 (m + 6) : ℤ) = PA309518.O3 (m + 3) + PA309518.GE (m + 6) := by
    exact_mod_cast PA309518.relD (m + 3)
  have hD_4 : (PA309518.E3 (m + 7) : ℤ) = PA309518.O3 (m + 4) + PA309518.GE (m + 7) := by
    exact_mod_cast PA309518.relD (m + 4)
  have hD_5 : (PA309518.E3 (m + 8) : ℤ) = PA309518.O3 (m + 5) + PA309518.GE (m + 8) := by
    exact_mod_cast PA309518.relD (m + 5)
  have hD_6 : (PA309518.E3 (m + 9) : ℤ) = PA309518.O3 (m + 6) + PA309518.GE (m + 9) := by
    exact_mod_cast PA309518.relD (m + 6)
  have hD_7 : (PA309518.E3 (m + 10) : ℤ) = PA309518.O3 (m + 7) + PA309518.GE (m + 10) := by
    exact_mod_cast PA309518.relD (m + 7)
  have hD_8 : (PA309518.E3 (m + 11) : ℤ) = PA309518.O3 (m + 8) + PA309518.GE (m + 11) := by
    exact_mod_cast PA309518.relD (m + 8)
  have hD_9 : (PA309518.E3 (m + 12) : ℤ) = PA309518.O3 (m + 9) + PA309518.GE (m + 12) := by
    exact_mod_cast PA309518.relD (m + 9)
  have hD_10 : (PA309518.E3 (m + 13) : ℤ) = PA309518.O3 (m + 10) + PA309518.GE (m + 13) := by
    exact_mod_cast PA309518.relD (m + 10)
  have hD_11 : (PA309518.E3 (m + 14) : ℤ) = PA309518.O3 (m + 11) + PA309518.GE (m + 14) := by
    exact_mod_cast PA309518.relD (m + 11)
  have hG_2 : (PA309518.GO (m + 4) : ℤ) + PA309518.GO (m + 2) + 2 = 2 * ((m : ℤ) + 2) + 3 * PA309518.Par (m + 2) := by
    exact_mod_cast PA309518.relG (m + 2) (by omega)
  have hG_4 : (PA309518.GO (m + 6) : ℤ) + PA309518.GO (m + 4) + 2 = 2 * ((m : ℤ) + 4) + 3 * PA309518.Par (m + 4) := by
    exact_mod_cast PA309518.relG (m + 4) (by omega)
  have hG_6 : (PA309518.GO (m + 8) : ℤ) + PA309518.GO (m + 6) + 2 = 2 * ((m : ℤ) + 6) + 3 * PA309518.Par (m + 6) := by
    exact_mod_cast PA309518.relG (m + 6) (by omega)
  have hG_8 : (PA309518.GO (m + 10) : ℤ) + PA309518.GO (m + 8) + 2 = 2 * ((m : ℤ) + 8) + 3 * PA309518.Par (m + 8) := by
    exact_mod_cast PA309518.relG (m + 8) (by omega)
  have hG_9 : (PA309518.GO (m + 11) : ℤ) + PA309518.GO (m + 9) + 2 = 2 * ((m : ℤ) + 9) + 3 * PA309518.Par (m + 9) := by
    exact_mod_cast PA309518.relG (m + 9) (by omega)
  have hH_2 : (PA309518.GE (m + 4) : ℤ) + PA309518.GE (m + 2) + 1 = ((m : ℤ) + 2) := by
    exact_mod_cast PA309518.relH (m + 2) (by omega)
  have hH_4 : (PA309518.GE (m + 6) : ℤ) + PA309518.GE (m + 4) + 1 = ((m : ℤ) + 4) := by
    exact_mod_cast PA309518.relH (m + 4) (by omega)
  have hH_6 : (PA309518.GE (m + 8) : ℤ) + PA309518.GE (m + 6) + 1 = ((m : ℤ) + 6) := by
    exact_mod_cast PA309518.relH (m + 6) (by omega)
  have hH_7 : (PA309518.GE (m + 9) : ℤ) + PA309518.GE (m + 7) + 1 = ((m : ℤ) + 7) := by
    exact_mod_cast PA309518.relH (m + 7) (by omega)
  have hH_8 : (PA309518.GE (m + 10) : ℤ) + PA309518.GE (m + 8) + 1 = ((m : ℤ) + 8) := by
    exact_mod_cast PA309518.relH (m + 8) (by omega)
  have hH_9 : (PA309518.GE (m + 11) : ℤ) + PA309518.GE (m + 9) + 1 = ((m : ℤ) + 9) := by
    exact_mod_cast PA309518.relH (m + 9) (by omega)
  have hH_10 : (PA309518.GE (m + 12) : ℤ) + PA309518.GE (m + 10) + 1 = ((m : ℤ) + 10) := by
    exact_mod_cast PA309518.relH (m + 10) (by omega)
  have hH_11 : (PA309518.GE (m + 13) : ℤ) + PA309518.GE (m + 11) + 1 = ((m : ℤ) + 11) := by
    exact_mod_cast PA309518.relH (m + 11) (by omega)
  have hH_12 : (PA309518.GE (m + 14) : ℤ) + PA309518.GE (m + 12) + 1 = ((m : ℤ) + 12) := by
    exact_mod_cast PA309518.relH (m + 12) (by omega)
  have hN2p_0 : 2 * (PA309518.N2 (m) : ℤ) + PA309518.Par (m) = (m : ℤ) + 2 := by
    exact_mod_cast PA309518.relN2p (m)
  have hP1_0 : (PA309518.Par (m + 1) : ℤ) + PA309518.Par (m) = 1 := by
    exact_mod_cast PA309518.relP1 (m)
  have hP2_1 : (PA309518.Par (m + 3) : ℤ) = PA309518.Par (m + 1) := by
    exact_mod_cast PA309518.relP2 (m + 1)
  have hP2_2 : (PA309518.Par (m + 4) : ℤ) = PA309518.Par (m + 2) := by
    exact_mod_cast PA309518.relP2 (m + 2)
  have hP2_3 : (PA309518.Par (m + 5) : ℤ) = PA309518.Par (m + 3) := by
    exact_mod_cast PA309518.relP2 (m + 3)
  have hP2_5 : (PA309518.Par (m + 7) : ℤ) = PA309518.Par (m + 5) := by
    exact_mod_cast PA309518.relP2 (m + 5)
  have hP2_6 : (PA309518.Par (m + 8) : ℤ) = PA309518.Par (m + 6) := by
    exact_mod_cast PA309518.relP2 (m + 6)
  have hP2_7 : (PA309518.Par (m + 9) : ℤ) = PA309518.Par (m + 7) := by
    exact_mod_cast PA309518.relP2 (m + 7)
  have hR2_0 : (PA309518.N2 (m + 1) : ℤ) + PA309518.N2 (m) = (m : ℤ) + 2 := by
    exact_mod_cast PA309518.relR2 (m)
  have hR2_1 : (PA309518.N2 (m + 2) : ℤ) + PA309518.N2 (m + 1) = ((m : ℤ) + 1) + 2 := by
    exact_mod_cast PA309518.relR2 (m + 1)
  have hR2_2 : (PA309518.N2 (m + 3) : ℤ) + PA309518.N2 (m + 2) = ((m : ℤ) + 2) + 2 := by
    exact_mod_cast PA309518.relR2 (m + 2)
  have hR2_3 : (PA309518.N2 (m + 4) : ℤ) + PA309518.N2 (m + 3) = ((m : ℤ) + 3) + 2 := by
    exact_mod_cast PA309518.relR2 (m + 3)
  have hR2_4 : (PA309518.N2 (m + 5) : ℤ) + PA309518.N2 (m + 4) = ((m : ℤ) + 4) + 2 := by
    exact_mod_cast PA309518.relR2 (m + 4)
  have hR2_5 : (PA309518.N2 (m + 6) : ℤ) + PA309518.N2 (m + 5) = ((m : ℤ) + 5) + 2 := by
    exact_mod_cast PA309518.relR2 (m + 5)
  have hR2_6 : (PA309518.N2 (m + 7) : ℤ) + PA309518.N2 (m + 6) = ((m : ℤ) + 6) + 2 := by
    exact_mod_cast PA309518.relR2 (m + 6)
  have hR3_3 : (PA309518.N3 (m + 6) : ℤ) = PA309518.N3 (m + 3) + PA309518.N2 (m + 3) := by
    exact_mod_cast PA309518.relR3 (m + 3)
  have hR3_4 : (PA309518.N3 (m + 7) : ℤ) = PA309518.N3 (m + 4) + PA309518.N2 (m + 4) := by
    exact_mod_cast PA309518.relR3 (m + 4)
  have hR3_5 : (PA309518.N3 (m + 8) : ℤ) = PA309518.N3 (m + 5) + PA309518.N2 (m + 5) := by
    exact_mod_cast PA309518.relR3 (m + 5)
  have hR3_6 : (PA309518.N3 (m + 9) : ℤ) = PA309518.N3 (m + 6) + PA309518.N2 (m + 6) := by
    exact_mod_cast PA309518.relR3 (m + 6)
  have hR3_7 : (PA309518.N3 (m + 10) : ℤ) = PA309518.N3 (m + 7) + PA309518.N2 (m + 7) := by
    exact_mod_cast PA309518.relR3 (m + 7)
  have hS2_2 : 2 * (PA309518.GO (m + 2) : ℤ) + 2 * PA309518.GE (m + 2) + 3 * PA309518.Par (m + 3) + 3 = 3 * ((m : ℤ) + 2) := by
    exact_mod_cast PA309518.relS2 (m + 2) (by omega)
  linear_combination ((-1 : ℤ)) * hA_0 + ((3 : ℤ)) * hA_1 + ((-4 : ℤ)) * hA_2 + ((4 : ℤ)) * hA_3 + ((-4 : ℤ)) *
    hA_4 + ((4 : ℤ)) * hA_5 + ((-3 : ℤ)) * hA_6 + ((1 : ℤ)) * hA_7 + ((-1 : ℤ)) * hB_4 + ((3 :
    ℤ)) * hB_5 + ((-4 : ℤ)) * hB_6 + ((4 : ℤ)) * hB_7 + ((-4 : ℤ)) * hB_8 + ((4 : ℤ)) * hB_9 +
    ((-3 : ℤ)) * hB_10 + ((1 : ℤ)) * hB_11 + ((1 : ℤ)) * hC_6 + ((-2 : ℤ)) * hC_7 + ((1 : ℤ)) *
    hC_8 + ((1 : ℤ)) * hD_3 + ((-3 : ℤ)) * hD_4 + ((4 : ℤ)) * hD_5 + ((-4 : ℤ)) * hD_6 + ((4 :
    ℤ)) * hD_7 + ((-4 : ℤ)) * hD_8 + ((4 : ℤ)) * hD_9 + ((-3 : ℤ)) * hD_10 + ((1 : ℤ)) * hD_11 +
    ((2 : ℤ)) * hG_2 + ((-2 : ℤ)) * hG_4 + ((2 : ℤ)) * hG_6 + ((-2 : ℤ)) * hG_8 + ((1 : ℤ)) *
    hG_9 + ((2 : ℤ)) * hH_2 + ((-2 : ℤ)) * hH_4 + ((3 : ℤ)) * hH_6 + ((-3 : ℤ)) * hH_7 + ((1 :
    ℤ)) * hH_8 + ((-1 : ℤ)) * hH_9 + ((3 : ℤ)) * hH_10 + ((-3 : ℤ)) * hH_11 + ((1 : ℤ)) * hH_12
    + ((-6 : ℤ)) * hN2p_0 + ((6 : ℤ)) * hP1_0 + ((6 : ℤ)) * hP2_1 + ((-6 : ℤ)) * hP2_2 + ((3 :
    ℤ)) * hP2_3 + ((3 : ℤ)) * hP2_5 + ((-6 : ℤ)) * hP2_6 + ((3 : ℤ)) * hP2_7 + ((12 : ℤ)) *
    hR2_0 + ((-12 : ℤ)) * hR2_1 + ((12 : ℤ)) * hR2_2 + ((-11 : ℤ)) * hR2_3 + ((8 : ℤ)) * hR2_4 +
    ((-4 : ℤ)) * hR2_5 + ((1 : ℤ)) * hR2_6 + ((1 : ℤ)) * hR3_3 + ((-3 : ℤ)) * hR3_4 + ((4 : ℤ))
    * hR3_5 + ((-3 : ℤ)) * hR3_6 + ((1 : ℤ)) * hR3_7 + ((-1 : ℤ)) * hS2_2
