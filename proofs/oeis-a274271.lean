import OMAStatements.S_oeis_a274271
import Mathlib

/-!
# A274271: closed form and recurrence

P3(N) = Σ_{c ≤ N/3} (floor((N - c)/2) + 1 - c) counts the partitions of N into at most three parts
and satisfies P3(N + 6) = P3(N) + N + 6, hence 12 P3(N) + 4 = (N + 3)^2 for N ≡ 1, 5 (mod 6) and
12 P3(N) = (N + 3)^2 for N ≡ 3 (mod 6). Removing the smallest part d from each of the four parts
gives P4(N) = Σ_{d ≤ N/4} P3(N - 4d), so P4(N + 12) = P4(N) + P3(N + 4) + P3(N + 8) + P3(N + 12).
Induction on q gives 144 P4(N) = N^3 + 15 N^2 + 63 N + 81 = (3 + N)^2 (9 + N) for
N = 12q + 3 and N = 12q + 9, and 3^n ≡ 3 or 9 (mod 12) for n ≥ 1. The recurrence follows since
1, 3, 9, 27 are the roots of x^4 - 40x^3 + 390x^2 - 1080x + 729.
-/

namespace PA274271

theorem icc_range' (k X : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc k X, f i = ∑ j ∈ Finset.range (X + 1 - k), f (k + j) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]

/-- Partitions of `N` into at most three parts. -/
def P3 (N : ℕ) : ℕ := ∑ c ∈ Finset.range (N / 3 + 1), ((N - c) / 2 + 1 - c)

/-- Partitions of `N` into at most four parts, sorted by their smallest part `d`. -/
def P4 (N : ℕ) : ℕ := ∑ d ∈ Finset.range (N / 4 + 1), P3 (N - 4 * d)

theorem count_eq (N : ℕ) :
    ∑ d ∈ Finset.range (N / 4 + 1), ∑ c ∈ Finset.Icc d ((N - d) / 3),
      ∑ _b ∈ Finset.Icc c ((N - c - d) / 2), 1 = P4 N := by
  unfold P4
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_range] at hd
  unfold P3
  rw [icc_range', show (N - d) / 3 + 1 - d = (N - 4 * d) / 3 + 1 by omega]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
  omega

theorem P3_six (N : ℕ) : P3 (N + 6) = P3 N + N + 6 := by
  unfold P3
  rw [show (N + 6) / 3 + 1 = N / 3 + 1 + 1 + 1 by omega, Finset.sum_range_succ,
    Finset.sum_range_succ]
  have h : ∑ c ∈ Finset.range (N / 3 + 1), ((N + 6 - c) / 2 + 1 - c) =
      ∑ c ∈ Finset.range (N / 3 + 1), (((N - c) / 2 + 1 - c) + 3) :=
    Finset.sum_congr rfl fun c hc => by
      rw [Finset.mem_range] at hc
      omega
  rw [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

theorem P3_odd (q : ℕ) : 12 * P3 (6 * q + 1) + 4 = (6 * q + 4) ^ 2 ∧
    12 * P3 (6 * q + 3) = (6 * q + 6) ^ 2 ∧ 12 * P3 (6 * q + 5) + 4 = (6 * q + 8) ^ 2 := by
  induction q with
  | zero => exact ⟨by decide, by decide, by decide⟩
  | succ q ih =>
    rw [show 6 * (q + 1) + 1 = 6 * q + 1 + 6 by ring, show 6 * (q + 1) + 3 = 6 * q + 3 + 6 by ring,
      show 6 * (q + 1) + 5 = 6 * q + 5 + 6 by ring, P3_six, P3_six, P3_six]
    exact ⟨by nlinarith [ih.1], by nlinarith [ih.2.1], by nlinarith [ih.2.2]⟩

theorem P4_twelve (N : ℕ) : P4 (N + 12) = P4 N + P3 (N + 4) + P3 (N + 8) + P3 (N + 12) := by
  unfold P4
  conv_lhs => rw [show (N + 12) / 4 + 1 = N / 4 + 1 + 1 + 1 + 1 by omega, Finset.sum_range_succ',
    Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∑ d ∈ Finset.range (N / 4 + 1), P3 (N + 12 - 4 * (d + 1 + 1 + 1)) =
      ∑ d ∈ Finset.range (N / 4 + 1), P3 (N - 4 * d) :=
    Finset.sum_congr rfl fun d _ => by rw [show N + 12 - 4 * (d + 1 + 1 + 1) = N - 4 * d by omega]
  rw [h, show N + 12 - 4 * (0 + 1 + 1) = N + 4 by omega, show N + 12 - 4 * (0 + 1) = N + 8 by omega,
    show N + 12 - 4 * 0 = N + 12 by omega]

theorem P4_closed39 (q : ℕ) :
    144 * P4 (12 * q + 3) = (12 * q + 3) ^ 3 + 15 * (12 * q + 3) ^ 2 + 63 * (12 * q + 3) + 81 ∧
    144 * P4 (12 * q + 9) = (12 * q + 9) ^ 3 + 15 * (12 * q + 9) ^ 2 + 63 * (12 * q + 9) + 81 := by
  induction q with
  | zero => exact ⟨by decide, by decide⟩
  | succ q ih =>
    have a1 := (P3_odd (2 * q + 1)).1
    have a2 := (P3_odd (2 * q + 1)).2.2
    have a3 := (P3_odd (2 * q + 2)).2.1
    have b1 := (P3_odd (2 * q + 2)).1
    have b2 := (P3_odd (2 * q + 2)).2.2
    have b3 := (P3_odd (2 * q + 3)).2.1
    rw [show 6 * (2 * q + 1) + 1 = 12 * q + 3 + 4 by ring] at a1
    rw [show 6 * (2 * q + 1) + 5 = 12 * q + 3 + 8 by ring] at a2
    rw [show 6 * (2 * q + 2) + 3 = 12 * q + 3 + 12 by ring] at a3
    rw [show 6 * (2 * q + 2) + 1 = 12 * q + 9 + 4 by ring] at b1
    rw [show 6 * (2 * q + 2) + 5 = 12 * q + 9 + 8 by ring] at b2
    rw [show 6 * (2 * q + 3) + 3 = 12 * q + 9 + 12 by ring] at b3
    rw [show 12 * (q + 1) + 3 = 12 * q + 3 + 12 by ring, show 12 * (q + 1) + 9 = 12 * q + 9 + 12 by ring,
      P4_twelve, P4_twelve]
    constructor
    · nlinarith [ih.1, a1, a2, a3]
    · nlinarith [ih.2, b1, b2, b3]

theorem pow_mod (n : ℕ) (hn : 1 ≤ n) : 3 ^ n % 12 = 3 ∨ 3 ^ n % 12 = 9 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      left
      norm_num
    · rw [pow_succ]
      rcases ih h with h' | h' <;> omega

theorem closed (n : ℕ) (hn : 1 ≤ n) : 144 * P4 (3 ^ n) = (3 + 3 ^ n) ^ 2 * (9 + 3 ^ n) := by
  rcases pow_mod n hn with h | h
  · have hq := (P4_closed39 (3 ^ n / 12)).1
    rw [show 12 * (3 ^ n / 12) + 3 = 3 ^ n by omega] at hq
    rw [hq]
    ring
  · have hq := (P4_closed39 (3 ^ n / 12)).2
    rw [show 12 * (3 ^ n / 12) + 9 = 3 ^ n by omega] at hq
    rw [hq]
    ring

theorem closed_int (n : ℕ) (hn : 1 ≤ n) :
    (144 : ℤ) * (P4 (3 ^ n) : ℤ) = (3 + 3 ^ n) ^ 2 * (9 + 3 ^ n) := by
  exact_mod_cast closed n hn

end PA274271

theorem OMA.solution : type_of% @OMA.S_oeis_a274271.main := by
  have aeq : ∀ n, OMA.S_oeis_a274271.a n = PA274271.P4 (3 ^ n) :=
    fun n => PA274271.count_eq (3 ^ n)
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rw [aeq]
    exact PA274271.closed n (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, aeq]
    have h5 := PA274271.closed_int (m + 5) (by omega)
    have h4 := PA274271.closed_int (m + 4) (by omega)
    have h3 := PA274271.closed_int (m + 3) (by omega)
    have h2 := PA274271.closed_int (m + 2) (by omega)
    have h1 := PA274271.closed_int (m + 1) (by omega)
    have key : (144 : ℤ) * ((PA274271.P4 (3 ^ (m + 5)) : ℤ) - 40 * PA274271.P4 (3 ^ (m + 4)) +
        390 * PA274271.P4 (3 ^ (m + 3)) - 1080 * PA274271.P4 (3 ^ (m + 2)) +
        729 * PA274271.P4 (3 ^ (m + 1))) = 0 := by
      linear_combination h5 - 40 * h4 + 390 * h3 - 1080 * h2 + 729 * h1
    linarith
