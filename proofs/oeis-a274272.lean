import OMAStatements.S_oeis_a274272
import Mathlib

/-!
# A274272: closed form and recurrence

P3(N) = Σ_{c ≤ N/3} (floor((N - c)/2) + 1 - c) counts the partitions of N into at most three parts
and satisfies P3(N + 6) = P3(N) + N + 6, hence 12 P3(N) + 4 = (N + 3)^2 for N ≡ 1, 5 (mod 6) and
12 P3(N) = (N + 3)^2 for N ≡ 3 (mod 6). Removing the smallest part d from each of the four parts
gives P4(N) = Σ_{d ≤ N/4} P3(N - 4d), so P4(N + 12) = P4(N) + P3(N + 4) + P3(N + 8) + P3(N + 12).
Induction on q gives 144 P4(N) = N^3 + 15 N^2 + 63 N + 65 for N = 12q + 1 and
144 P4(N) = N^3 + 15 N^2 + 63 N + 49 for N = 12q + 5; 5^n ≡ 1 (mod 12) for even n and ≡ 5 for odd
n, which gives the closed form. The recurrence follows since 1, -1, 5, 25, 125 are the roots of
its characteristic polynomial.
-/

namespace PA274272

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

theorem P4_closed15 (q : ℕ) :
    144 * P4 (12 * q + 1) = (12 * q + 1) ^ 3 + 15 * (12 * q + 1) ^ 2 + 63 * (12 * q + 1) + 65 ∧
    144 * P4 (12 * q + 5) = (12 * q + 5) ^ 3 + 15 * (12 * q + 5) ^ 2 + 63 * (12 * q + 5) + 49 := by
  induction q with
  | zero => exact ⟨by decide, by decide⟩
  | succ q ih =>
    have a1 := (P3_odd (2 * q)).2.2
    have a2 := (P3_odd (2 * q + 1)).2.1
    have a3 := (P3_odd (2 * q + 2)).1
    have b1 := (P3_odd (2 * q + 1)).2.1
    have b2 := (P3_odd (2 * q + 2)).1
    have b3 := (P3_odd (2 * q + 2)).2.2
    rw [show 6 * (2 * q) + 5 = 12 * q + 1 + 4 by ring] at a1
    rw [show 6 * (2 * q + 1) + 3 = 12 * q + 1 + 8 by ring] at a2
    rw [show 6 * (2 * q + 2) + 1 = 12 * q + 1 + 12 by ring] at a3
    rw [show 6 * (2 * q + 1) + 3 = 12 * q + 5 + 4 by ring] at b1
    rw [show 6 * (2 * q + 2) + 1 = 12 * q + 5 + 8 by ring] at b2
    rw [show 6 * (2 * q + 2) + 5 = 12 * q + 5 + 12 by ring] at b3
    rw [show 12 * (q + 1) + 1 = 12 * q + 1 + 12 by ring, show 12 * (q + 1) + 5 = 12 * q + 5 + 12 by ring,
      P4_twelve, P4_twelve]
    constructor
    · nlinarith [ih.1, a1, a2, a3]
    · nlinarith [ih.2, b1, b2, b3]

theorem pow_mod (n : ℕ) :
    (5 ^ n % 12 = 1 ∧ (-1 : ℤ) ^ n = 1) ∨ (5 ^ n % 12 = 5 ∧ (-1 : ℤ) ^ n = -1) := by
  induction n with
  | zero => left; norm_num
  | succ n ih =>
    rw [pow_succ, pow_succ]
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      exact ⟨by omega, by rw [h2]; norm_num⟩
    · left
      exact ⟨by omega, by rw [h2]; norm_num⟩

theorem closed (n : ℕ) :
    144 * (P4 (5 ^ n) : ℤ) = 57 + 8 * (-1) ^ n + 63 * 5 ^ n + 3 * 5 ^ (1 + 2 * n) + 125 ^ n := by
  have e1 : (5 : ℤ) ^ (1 + 2 * n) = 5 * ((5 : ℤ) ^ n) ^ 2 := by
    rw [show 1 + 2 * n = 1 + n * 2 by ring, pow_add, pow_mul, pow_one]
  have e2 : (125 : ℤ) ^ n = ((5 : ℤ) ^ n) ^ 3 := by
    rw [show (125 : ℤ) = 5 ^ 3 by norm_num, ← pow_mul, mul_comm, pow_mul]
  rw [e1, e2]
  rcases pow_mod n with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hq := (P4_closed15 (5 ^ n / 12)).1
    rw [show 12 * (5 ^ n / 12) + 1 = 5 ^ n by omega] at hq
    have hz : (144 : ℤ) * (P4 (5 ^ n) : ℤ) =
        ((5 ^ n : ℕ) : ℤ) ^ 3 + 15 * ((5 ^ n : ℕ) : ℤ) ^ 2 + 63 * ((5 ^ n : ℕ) : ℤ) + 65 := by
      exact_mod_cast hq
    push_cast at hz
    rw [h2]
    linear_combination hz
  · have hq := (P4_closed15 (5 ^ n / 12)).2
    rw [show 12 * (5 ^ n / 12) + 5 = 5 ^ n by omega] at hq
    have hz : (144 : ℤ) * (P4 (5 ^ n) : ℤ) =
        ((5 ^ n : ℕ) : ℤ) ^ 3 + 15 * ((5 ^ n : ℕ) : ℤ) ^ 2 + 63 * ((5 ^ n : ℕ) : ℤ) + 49 := by
      exact_mod_cast hq
    push_cast at hz
    rw [h2]
    linear_combination hz

end PA274272

theorem OMA.solution : type_of% @OMA.S_oeis_a274272.main := by
  have aeq : ∀ n, OMA.S_oeis_a274272.a n = PA274272.P4 (5 ^ n) :=
    fun n => PA274272.count_eq (5 ^ n)
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · rw [aeq]
    exact PA274272.closed n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega,
      aeq]
    have h5 := PA274272.closed (m + 5)
    have h4 := PA274272.closed (m + 4)
    have h3 := PA274272.closed (m + 3)
    have h2 := PA274272.closed (m + 2)
    have h1 := PA274272.closed (m + 1)
    have h0 := PA274272.closed m
    have key : (144 : ℤ) * ((PA274272.P4 (5 ^ (m + 5)) : ℤ) - 155 * PA274272.P4 (5 ^ (m + 4)) +
        3874 * PA274272.P4 (5 ^ (m + 3)) - 15470 * PA274272.P4 (5 ^ (m + 2)) -
        3875 * PA274272.P4 (5 ^ (m + 1)) + 15625 * PA274272.P4 (5 ^ m)) = 0 := by
      linear_combination h5 - 155 * h4 + 3874 * h3 - 15470 * h2 - 3875 * h1 + 15625 * h0
    linarith
