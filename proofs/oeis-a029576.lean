import OMAStatements.S_oeis_a029576

-- Problem: A029576: Number of permutations of an n-set containing a 9-cycle.
-- Upstream: formal-conjectures statements/oeis-a029576.lean:0 (declaration OMA.S_oeis_a029576.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write t(m) for the partial sum Sum_{k=0..m} (-1)^k/(9^k k!), so that a(n) = n! (1 - t(floor(n/9))).
If 9 does not divide n then floor(n/9) = floor((n-1)/9), which gives (1). By induction
S(k) = 9^k k! (1 - t(k)), and S(k) ≥ 1 for k ≥ 1; substituting this in (2) reduces it to
(9 k)! = 9 k (9 k - 1)!. -/

namespace A029576Aux

open OMA.S_oeis_a029576

/-- The partial sums t(m) = Sum_{k=0..m} (-1)^k/(9^k k!). -/
def t (m : ℕ) : ℚ := ∑ k ∈ Finset.range (m + 1), (-1 : ℚ) ^ k / (9 ^ k * (k.factorial : ℚ))

theorem t_succ (m : ℕ) :
    t (m + 1) = t m + (-1 : ℚ) ^ (m + 1) / (9 ^ (m + 1) * ((m + 1).factorial : ℚ)) := by
  unfold t
  rw [Finset.sum_range_succ]

theorem a_eq (n : ℕ) : a n = (n.factorial : ℚ) * (1 - t (n / 9)) := rfl

theorem U (k : ℕ) : S k = 9 ^ k * (k.factorial : ℚ) * (1 - t k) := by
  induction k with
  | zero => simp [S, t]
  | succ k ih =>
    rw [S, ih, t_succ, Nat.factorial_succ]
    have hk : (k.factorial : ℚ) ≠ 0 := by positivity
    have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem Spos (i : ℕ) : (1 : ℚ) ≤ S (i + 1) := by
  induction i with
  | zero => norm_num [S]
  | succ i ih =>
    rw [S]
    have h1 : (-1 : ℚ) ^ (i + 1 + 1) ≤ 1 := by
      rcases neg_one_pow_eq_or ℚ (i + 1 + 1) with h | h
      · exact le_of_eq h
      · rw [h]
        norm_num
    have hi : (0 : ℚ) ≤ (i : ℚ) := Nat.cast_nonneg i
    have hS0 : (0 : ℚ) ≤ S (i + 1) := by linarith
    have hp := mul_nonneg hi hS0
    push_cast
    nlinarith

theorem part1 (n : ℕ) (hn : 9 < n) (h : n % 9 ≠ 0) : a n = (n : ℚ) * a (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : (m + 1) / 9 = m / 9 := by omega
  rw [a_eq, a_eq, Nat.add_sub_cancel, e, Nat.factorial_succ]
  push_cast
  ring

theorem part2 (k : ℕ) (hk : 1 < k) : a (9 * k) = a (9 * k - 1) * S k / S (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hS : S (i + 1) ≠ 0 := by
    have := Spos i
    intro h0
    rw [h0] at this
    norm_num at this
  rw [Nat.add_sub_cancel, eq_div_iff hS, U (i + 1 + 1), U (i + 1), a_eq, a_eq]
  have e1 : 9 * (i + 1 + 1) / 9 = i + 1 + 1 := by omega
  have e2 : (9 * (i + 1 + 1) - 1) / 9 = i + 1 := by omega
  have e3 : 9 * (i + 1 + 1) - 1 = 9 * (i + 1) + 8 := by omega
  have e4 : 9 * (i + 1 + 1) = 9 * (i + 1) + 8 + 1 := by omega
  rw [e1, e2, e3, e4, Nat.factorial_succ (9 * (i + 1) + 8), Nat.factorial_succ (i + 1)]
  push_cast
  ring

end A029576Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a029576.main :=
  ⟨fun n hn h => A029576Aux.part1 n hn h, fun k hk => A029576Aux.part2 k hk⟩
