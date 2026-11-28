import OMAStatements.S_oeis_a307872
import Mathlib

/-!
# A307872: Barker's recurrence

The inner sum has c(n,k) = floor((n−k)/2) − k + 1 terms, so a(n) = S(n) = Σ_k k·c(n,k). Shifting
k ↦ k + 1 (adding 1 to every part) gives c(n+3, k+1) = c(n, k), hence
S(n+3) = S(n) + N(n) + F(n) and N(n+3) = N(n) + F(n), where N(n) = Σ_k c(n,k) counts the
partitions and F(n) = floor((n+2)/2) counts those with smallest part 1; also F(n+2) = F(n) + 1.
Barker's operator (E−1)(E²−1)(E³−1)² annihilates S by these three relations (an explicit linear
combination of their shifts).
-/

namespace PA307872
open OMA.S_oeis_a307872

theorem icc_range (m : ℕ) (f : ℕ → ℕ) : ∑ k ∈ Finset.Icc 1 m, f k = ∑ t ∈ Finset.range m, f (t + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- The number of partitions counted at smallest part `k`. -/
def c (n k : ℕ) : ℕ := (n - k) / 2 + 1 - k

def S (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n / 3), (t + 1) * c n (t + 1)

def N (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n / 3), c n (t + 1)

theorem a_eq (n : ℕ) : a n = S n := by
  unfold a S
  rw [icc_range (n / 3) (fun k => ∑ _i ∈ Finset.Icc k ((n - k) / 2), k)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_comm]
  rfl

theorem shift (n t : ℕ) (ht : t < n / 3) : c (n + 3) (t + 2) = c n (t + 1) := by
  unfold c; omega

theorem S_succ (n : ℕ) : S (n + 3) = (n + 2) / 2 + S n + N n := by
  unfold S N
  rw [show (n + 3) / 3 = n / 3 + 1 by omega, Finset.sum_range_succ']
  have h : ∀ t ∈ Finset.range (n / 3), (t + 1 + 1) * c (n + 3) (t + 1 + 1) =
      (t + 1) * c n (t + 1) + c n (t + 1) := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [show t + 1 + 1 = t + 2 by ring, shift n t ht]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  have h1 : (0 + 1) * c (n + 3) (0 + 1) = (n + 2) / 2 := by unfold c; omega
  rw [h1]
  ring

theorem N_succ (n : ℕ) : N (n + 3) = (n + 2) / 2 + N n := by
  unfold N
  rw [show (n + 3) / 3 = n / 3 + 1 by omega, Finset.sum_range_succ']
  have h : ∀ t ∈ Finset.range (n / 3), c (n + 3) (t + 1 + 1) = c n (t + 1) := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [show t + 1 + 1 = t + 2 by ring, shift n t ht]
  rw [Finset.sum_congr rfl h]
  have h1 : c (n + 3) (0 + 1) = (n + 2) / 2 := by unfold c; omega
  rw [h1]
  ring

theorem R1 (n : ℕ) : ((S (n + 3) : ℕ) : ℤ) = (S n : ℤ) + (N n : ℤ) + (((n + 2) / 2 : ℕ) : ℤ) := by
  rw [S_succ]; push_cast; ring

theorem R2 (n : ℕ) : ((N (n + 3) : ℕ) : ℤ) = (N n : ℤ) + (((n + 2) / 2 : ℕ) : ℤ) := by
  rw [N_succ]; push_cast; ring

theorem R3 (n : ℕ) : (((n + 2 + 2) / 2 : ℕ) : ℤ) = (((n + 2) / 2 : ℕ) : ℤ) + 1 := by
  have : (n + 2 + 2) / 2 = (n + 2) / 2 + 1 := by omega
  rw [this]; push_cast; ring

end PA307872

theorem OMA.solution : type_of% @OMA.S_oeis_a307872.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  simp only [PA307872.a_eq, show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
    show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega,
    show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega,
    show m + 9 - 9 = m by omega]
  have r10 := PA307872.R1 (m + 0)
  have r11 := PA307872.R1 (m + 1)
  have r12 := PA307872.R1 (m + 2)
  have r13 := PA307872.R1 (m + 3)
  have r14 := PA307872.R1 (m + 4)
  have r15 := PA307872.R1 (m + 5)
  have r16 := PA307872.R1 (m + 6)
  have r20 := PA307872.R2 (m + 0)
  have r21 := PA307872.R2 (m + 1)
  have r22 := PA307872.R2 (m + 2)
  have r23 := PA307872.R2 (m + 3)
  have r30 := PA307872.R3 (m + 0)
  have r31 := PA307872.R3 (m + 1)
  have r32 := PA307872.R3 (m + 2)
  have r33 := PA307872.R3 (m + 3)
  have r34 := PA307872.R3 (m + 4)
  ring_nf at *
  linear_combination (-1 : ℤ) * r10 + (1 : ℤ) * r11 + (1 : ℤ) * r12 + (-1 : ℤ) * r14 + (-1 : ℤ) * r15 + (1 : ℤ) * r16 + (1 : ℤ) * r20 + (-1 : ℤ) * r21 + (-1 : ℤ) * r22 + (1 : ℤ) * r23 + (-1 : ℤ) * r33 + (1 : ℤ) * r34
