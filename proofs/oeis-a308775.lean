import OMAStatements.S_oeis_a308775
import Mathlib

/-!
# A308775: Barker's recurrence

Every partition of n into 4 parts has part sum n, so a(n) = n * N4(n) with N4(n) the number of
partitions of n into 4 parts. Write C3(r, k) for the number of partitions of r into 3 parts that are
all at least k. Adding 1 to every part gives C3(r + 3, k + 1) = C3(r, k), and removing the smallest
part 1 leaves a partition into one part fewer, so
N4(m + 4) = N4(m) + N3(m + 3), N3(r + 3) = N3(r) + N2(r) and N2(r + 2) = N2(r) + 1,
where N3(r) = C3(r, 1) and N2(r) = floor((r + 2)/2) counts the partitions of r + 2 into 2 parts.
Barker's operator applied to n * N4(n) is an explicit combination of these relations with
coefficients linear in n.
-/

namespace PA308775

theorem icc_range (m : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 m, f k = ∑ t ∈ Finset.range m, f (t + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem icc_range' (k X : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc k X, f i = ∑ j ∈ Finset.range (X + 1 - k), f (k + j) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]

/-- Number of `i` with `j ≤ i ≤ r - j - i`. -/
def L3 (r j : ℕ) : ℕ := (r - j) / 2 + 1 - j

/-- Number of partitions of `r` into 3 parts, all at least `k`. -/
def C3 (r k : ℕ) : ℕ := ∑ s ∈ Finset.range (r / 3 + 1 - k), L3 r (k + s)

def N4 (m : ℕ) : ℕ := ∑ t ∈ Finset.range (m / 4), C3 (m - (t + 1)) (t + 1)

def N3 (r : ℕ) : ℕ := C3 r 1

def N2 (r : ℕ) : ℕ := (r + 2) / 2

theorem a_eq (n : ℕ) : OMA.S_oeis_a308775.a n = n * N4 n := by
  unfold OMA.S_oeis_a308775.a N4
  rw [icc_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold C3
  rw [icc_range', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => n) fun i hi => by rw [Finset.mem_Icc] at hi; omega,
    Finset.sum_const, Nat.card_Icc, smul_eq_mul]
  unfold L3
  rw [show (n - (t + 1 + s) - (t + 1)) / 2 + 1 - (t + 1 + s) =
    (n - (t + 1) - (t + 1 + s)) / 2 + 1 - (t + 1 + s) by omega]
  ring

theorem C3_shift (r k : ℕ) : C3 (r + 3) (k + 1) = C3 r k := by
  unfold C3
  rw [show (r + 3) / 3 + 1 - (k + 1) = r / 3 + 1 - k by omega]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold L3
  omega

theorem N4_succ (m : ℕ) : N4 (m + 4) = N4 m + N3 (m + 3) := by
  unfold N4 N3
  rw [show (m + 4) / 4 = m / 4 + 1 by omega, Finset.sum_range_succ',
    show m + 4 - (0 + 1) = m + 3 by omega]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [show m + 4 - (t + 1 + 1) = m - (t + 1) + 3 by omega]
  exact C3_shift _ _

theorem N3_succ (r : ℕ) : N3 (r + 3) = N3 r + N2 r := by
  unfold N3 C3 N2
  rw [show (r + 3) / 3 + 1 - 1 = r / 3 + 1 - 1 + 1 by omega, Finset.sum_range_succ']
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold L3
  omega

theorem N2_succ (r : ℕ) : N2 (r + 2) = N2 r + 1 := by
  unfold N2
  omega

theorem R4_int (m : ℕ) : (N4 (m + 4) : ℤ) = (N4 m : ℤ) + (N3 (m + 3) : ℤ) := by
  exact_mod_cast N4_succ m

theorem R3_int (r : ℕ) : (N3 (r + 3) : ℤ) = (N3 r : ℤ) + (N2 r : ℤ) := by
  exact_mod_cast N3_succ r

theorem R2_int (r : ℕ) : (N2 (r + 2) : ℤ) = (N2 r : ℤ) + 1 := by
  exact_mod_cast N2_succ r

end PA308775

theorem OMA.solution : type_of% @OMA.S_oeis_a308775.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 16 := ⟨n - 16, by omega⟩
  simp only [show m + 16 - 2 = m + 14 by omega, show m + 16 - 3 = m + 13 by omega, show m + 16 - 4 = m
    + 12 by omega, show m + 16 - 5 = m + 11 by omega, show m + 16 - 6 = m + 10 by omega, show
    m + 16 - 7 = m + 9 by omega, show m + 16 - 9 = m + 7 by omega, show m + 16 - 10 = m + 6 by
    omega, show m + 16 - 11 = m + 5 by omega, show m + 16 - 12 = m + 4 by omega, show m + 16 -
    13 = m + 3 by omega, show m + 16 - 14 = m + 2 by omega, show m + 16 - 16 = m + 0 by omega, PA308775.a_eq]
  push_cast
  have hR2_3 := PA308775.R2_int (m + 3)
  have hR2_5 := PA308775.R2_int (m + 5)
  have hR2_6 := PA308775.R2_int (m + 6)
  have hR2_7 := PA308775.R2_int (m + 7)
  have hR2_8 := PA308775.R2_int (m + 8)
  have hR2_10 := PA308775.R2_int (m + 10)
  have hR3_3 := PA308775.R3_int (m + 3)
  have hR3_5 := PA308775.R3_int (m + 5)
  have hR3_6 := PA308775.R3_int (m + 6)
  have hR3_7 := PA308775.R3_int (m + 7)
  have hR3_8 := PA308775.R3_int (m + 8)
  have hR3_9 := PA308775.R3_int (m + 9)
  have hR3_10 := PA308775.R3_int (m + 10)
  have hR3_12 := PA308775.R3_int (m + 12)
  have hR4_0 := PA308775.R4_int (m + 0)
  have hR4_2 := PA308775.R4_int (m + 2)
  have hR4_3 := PA308775.R4_int (m + 3)
  have hR4_4 := PA308775.R4_int (m + 4)
  have hR4_5 := PA308775.R4_int (m + 5)
  have hR4_6 := PA308775.R4_int (m + 6)
  have hR4_7 := PA308775.R4_int (m + 7)
  have hR4_8 := PA308775.R4_int (m + 8)
  have hR4_9 := PA308775.R4_int (m + 9)
  have hR4_10 := PA308775.R4_int (m + 10)
  have hR4_12 := PA308775.R4_int (m + 12)
  ring_nf at *
  linear_combination ((1 : ℤ) * (m : ℤ)) * hR2_3 + ((-2 : ℤ)) * hR2_5 + ((-6 : ℤ) + (-1 : ℤ) * (m : ℤ)) * hR2_6 + ((-10 : ℤ) + (-1 : ℤ) * (m : ℤ)) * hR2_7 + ((2 : ℤ)) * hR2_8 + ((16 : ℤ) + (1 : ℤ) * (m : ℤ)) * hR2_10 + ((-1 : ℤ) * (m : ℤ)) * hR3_3 + ((2 : ℤ) + (1 : ℤ) * (m : ℤ)) * hR3_5 + ((6 : ℤ) + (1 : ℤ) * (m : ℤ)) * hR3_6 + ((8 : ℤ) + (1 : ℤ) * (m : ℤ)) * hR3_7 + ((-8 : ℤ) + (-1 : ℤ) * (m : ℤ)) * hR3_8 + ((-10 : ℤ) + (-1 : ℤ) * (m : ℤ)) * hR3_9 + ((-14 : ℤ) + (-1 : ℤ) * (m : ℤ)) * hR3_10 + ((16 : ℤ) + (1 : ℤ) * (m : ℤ)) * hR3_12 + ((1 : ℤ) * (m : ℤ)) * hR4_0 + ((-2 : ℤ) + (-1 : ℤ) * (m : ℤ)) * hR4_2 + ((-6 : ℤ) + (-2 : ℤ) * (m : ℤ)) * hR4_3 + ((-8 : ℤ) + (-1 : ℤ) * (m : ℤ)) * hR4_4 + ((10 : ℤ) + (2 : ℤ) * (m : ℤ)) * hR4_5 + ((16 : ℤ) + (2 : ℤ) * (m : ℤ)) * hR4_6 + ((22 : ℤ) + (2 : ℤ) * (m : ℤ)) * hR4_7 + ((-8 : ℤ) + (-1 : ℤ) * (m : ℤ)) * hR4_8 + ((-26 : ℤ) + (-2 : ℤ) * (m : ℤ)) * hR4_9 + ((-14 : ℤ) + (-1 : ℤ) * (m : ℤ)) * hR4_10 + ((16 : ℤ) + (1 : ℤ) * (m : ℤ)) * hR4_12
