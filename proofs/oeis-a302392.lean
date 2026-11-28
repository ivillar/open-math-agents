import OMAStatements.S_oeis_a302392
import Mathlib

/-!
# A302392: Barker's recurrence

Write a partition of m into 3 parts as (k, k + j, m - (k + j) - k). Adding 1 to every part maps the
partitions of m bijectively onto the partitions of m + 3 with smallest part at least 2, and it swaps
odd and even parts. Hence, with O(m) and E(m) the total numbers of odd and even parts and
GO(m), GE(m) the corresponding counts over the partitions with smallest part 1,
O(m + 3) = GO(m + 3) + E(m) and E(m + 3) = GE(m + 3) + O(m), so
a(n + 2) = a(n) + u(n) with u(n) = GO(3n + 6) + GE(3n + 3). The partitions (1, 1 + j, m - 2 - j)
contribute periodically, giving GO(m + 12) = GO(m) + 12 and GE(m + 12) = GE(m) + 6, so
u(n + 4) = u(n) + 18. Barker's operator is (E^5 - E^4 - E + 1)(E^2 - 1), and these two relations
annihilate it.
-/

namespace PA302392

theorem icc_range (m : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.Icc 1 m, f k = ∑ t ∈ Finset.range m, f (t + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem icc_range' (k X : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc k X, f i = ∑ j ∈ Finset.range (X + 1 - k), f (k + j) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]

/-- Number of odd parts among `x, y, z`. -/
def wo (x y z : ℕ) : ℕ := x % 2 + y % 2 + z % 2

/-- Number of even parts among `x, y, z`. -/
def we (x y z : ℕ) : ℕ := (x + 1) % 2 + (y + 1) % 2 + (z + 1) % 2

def GO (m k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range ((m - k) / 2 + 1 - k), wo k (k + j) (m - (k + j) - k)

def GE (m k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range ((m - k) / 2 + 1 - k), we k (k + j) (m - (k + j) - k)

def FO (m : ℕ) : ℕ := ∑ t ∈ Finset.range (m / 3), GO m (t + 1)

def FE (m : ℕ) : ℕ := ∑ t ∈ Finset.range (m / 3), GE m (t + 1)

def u (n : ℕ) : ℕ := GO (3 * n + 6) 1 + GE (3 * n + 3) 1

theorem a_eq (n : ℕ) : OMA.S_oeis_a302392.a n = FO (3 * n) := by
  unfold OMA.S_oeis_a302392.a FO
  rw [show 3 * n / 3 = n by omega, icc_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [icc_range']
  rfl

theorem GO_shift (m t : ℕ) : GO (m + 3) (t + 2) = GE m (t + 1) := by
  unfold GO GE
  rw [show (m + 3 - (t + 2)) / 2 + 1 - (t + 2) = (m - (t + 1)) / 2 + 1 - (t + 1) by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  unfold wo we
  omega

theorem GE_shift (m t : ℕ) : GE (m + 3) (t + 2) = GO m (t + 1) := by
  unfold GO GE
  rw [show (m + 3 - (t + 2)) / 2 + 1 - (t + 2) = (m - (t + 1)) / 2 + 1 - (t + 1) by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  unfold wo we
  omega

theorem FO_succ (m : ℕ) : FO (m + 3) = GO (m + 3) 1 + FE m := by
  unfold FO FE
  rw [show (m + 3) / 3 = m / 3 + 1 by omega, Finset.sum_range_succ', add_comm]
  congr 1
  exact Finset.sum_congr rfl fun t _ => GO_shift m t

theorem FE_succ (m : ℕ) : FE (m + 3) = GE (m + 3) 1 + FO m := by
  unfold FO FE
  rw [show (m + 3) / 3 = m / 3 + 1 by omega, Finset.sum_range_succ', add_comm]
  congr 1
  exact Finset.sum_congr rfl fun t _ => GE_shift m t

theorem step (n : ℕ) : FO (3 * n + 6) = FO (3 * n) + u n := by
  rw [show 3 * n + 6 = 3 * n + 3 + 3 by omega, FO_succ, FE_succ]
  unfold u
  rw [show 3 * n + 3 + 3 = 3 * n + 6 by omega]
  ring

theorem GO_twelve (m : ℕ) (hm : 1 ≤ m) : GO (m + 12) 1 = GO m 1 + 12 := by
  unfold GO
  rw [show (m + 12 - 1) / 2 + 1 - 1 = (m - 1) / 2 + 1 - 1 + 6 by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have hs : ∑ x ∈ Finset.range ((m - 1) / 2 + 1 - 1), wo 1 (1 + x) (m + 12 - (1 + x) - 1) =
      ∑ x ∈ Finset.range ((m - 1) / 2 + 1 - 1), wo 1 (1 + x) (m - (1 + x) - 1) :=
    Finset.sum_congr rfl fun x hx => by
      rw [Finset.mem_range] at hx
      unfold wo
      omega
  rw [hs]
  unfold wo
  omega

theorem GE_twelve (m : ℕ) (hm : 1 ≤ m) : GE (m + 12) 1 = GE m 1 + 6 := by
  unfold GE
  rw [show (m + 12 - 1) / 2 + 1 - 1 = (m - 1) / 2 + 1 - 1 + 6 by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have hs : ∑ x ∈ Finset.range ((m - 1) / 2 + 1 - 1), we 1 (1 + x) (m + 12 - (1 + x) - 1) =
      ∑ x ∈ Finset.range ((m - 1) / 2 + 1 - 1), we 1 (1 + x) (m - (1 + x) - 1) :=
    Finset.sum_congr rfl fun x hx => by
      rw [Finset.mem_range] at hx
      unfold we
      omega
  rw [hs]
  unfold we
  omega

theorem u_four (n : ℕ) : u (n + 4) = u n + 18 := by
  unfold u
  rw [show 3 * (n + 4) + 6 = 3 * n + 6 + 12 by ring, show 3 * (n + 4) + 3 = 3 * n + 3 + 12 by ring,
    GO_twelve _ (by omega), GE_twelve _ (by omega)]
  ring

theorem step_int (n : ℕ) : (FO (3 * n + 6) : ℤ) = (FO (3 * n) : ℤ) + (u n : ℤ) := by
  exact_mod_cast step n

theorem u_four_int (n : ℕ) : (u (n + 4) : ℤ) = (u n : ℤ) + 18 := by
  exact_mod_cast u_four n

end PA302392

theorem OMA.solution : type_of% @OMA.S_oeis_a302392.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
    show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
    show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega,
    show m + 8 - 7 = m + 1 by omega, PA302392.a_eq]
  have r0 := PA302392.step_int (m + 1)
  have r1 := PA302392.step_int (m + 2)
  have r4 := PA302392.step_int (m + 5)
  have r5 := PA302392.step_int (m + 6)
  have q0 := PA302392.u_four_int (m + 1)
  have q1 := PA302392.u_four_int (m + 2)
  ring_nf at *
  linear_combination r0 - r1 - r4 + r5 + q1 - q0
