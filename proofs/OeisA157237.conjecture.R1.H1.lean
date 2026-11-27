import OMAReductions.R_OeisA157237_conjecture_R1
import Mathlib

-- Step OeisA157237.conjecture.R1.H1: hypothesis H1 of reduction OeisA157237.conjecture.R1
-- Credit: @ivillar (original proof).
-- Strategy. Only x, y < 18 can satisfy 2^x + 11*2^y < N <= 2^17. A Boolean checker, evaluated by
-- decide +kernel, verifies for each listed n that every remaining candidate is below 2, not 1 mod 6,
-- or has a divisor in [2, 400); a soundness lemma then makes every summand of a(n) vanish.

namespace OMA.OeisA157237H1

/-- Every candidate `N - (2^x + 11 2^y)` below `N` is either small, not `1 mod 6`, or has a
divisor in `[2, 400)` below itself. -/
def chk (N : ℕ) : Bool :=
  (List.range 18).all fun x => (List.range 18).all fun y =>
    decide (x = 0) || decide (y = 0) || decide (N ≤ 2 ^ x + 11 * 2 ^ y) || decide (N - (2 ^ x + 11 * 2 ^ y) < 2) ||
    ((N - (2 ^ x + 11 * 2 ^ y)) % 6 != 1) ||
    (List.range 400).any fun d =>
      decide (2 ≤ d) && decide (d < N - (2 ^ x + 11 * 2 ^ y)) &&
        ((N - (2 ^ x + 11 * 2 ^ y)) % d == 0)

lemma not_prime_of_dvd {m d : ℕ} (h2 : 2 ≤ d) (hd : d < m) (hm : m % d = 0) : ¬ m.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hm) with h | h <;> omega

lemma chk_sound (N : ℕ) (hN : N ≤ 2 ^ 17) (h : chk N = true) (x y : ℕ) (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) :
    ¬ (2 ^ x + 11 * 2 ^ y < N ∧ (N - (2 ^ x + 11 * 2 ^ y)).Prime ∧
      (N - (2 ^ x + 11 * 2 ^ y)) % 6 = 1) := by
  rintro ⟨hlt, hp, h6⟩
  have h0x : 0 < 2 ^ x := by positivity
  have h0y : 0 < 2 ^ y := by positivity
  have hx : x < 18 := by
    by_contra hx
    have : 2 ^ 18 ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hy : y < 18 := by
    by_contra hy
    have : 2 ^ 18 ≤ 2 ^ y := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  unfold chk at h
  rw [List.all_eq_true] at h
  have h1 := h x (List.mem_range.mpr hx)
  rw [List.all_eq_true] at h1
  have h2 := h1 y (List.mem_range.mpr hy)
  simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, List.any_eq_true,
    List.mem_range, Bool.and_eq_true, beq_iff_eq] at h2
  rcases h2 with ((((h3 | h3) | h3) | h3) | h3) | ⟨d, _, ⟨hd2, hdm⟩, hmod⟩
  · omega
  · omega
  · omega
  · exact absurd hp (by
      intro hp'
      have := hp'.two_le
      omega)
  · exact h3 h6
  · exact not_prime_of_dvd hd2 hdm hmod hp

lemma a_eq_zero (n : ℕ) (hN : 2 * n - 1 ≤ 2 ^ 17) (h : chk (2 * n - 1) = true) :
    OeisA157237.a n = 0 := by
  unfold OeisA157237.a
  split_ifs with hn
  · rfl
  · apply Finset.sum_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro y hy
    rw [Finset.mem_Icc] at hx hy
    rw [if_neg (chk_sound (2 * n - 1) hN h x y hx.1 hy.1)]

end OMA.OeisA157237H1

theorem OMA.solution : OMA.R_OeisA157237_conjecture_R1.H1 := by
  intro n hn
  have hall : ∀ m ∈ ((List.range 16) ++ [18, 21, 24, 51, 84, 1011, 59586]),
      OMA.OeisA157237H1.chk (2 * m - 1) = true := by
    decide +kernel
  have hmem : n ∈ ((List.range 16) ++ [18, 21, 24, 51, 84, 1011, 59586]) := by
    rcases hn with hn | hn
    · exact List.mem_append_left _ (List.mem_range.mpr (by omega))
    · apply List.mem_append_right
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hbound : 2 * n - 1 ≤ 2 ^ 17 := by
    rcases hn with hn | hn
    · omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  exact OMA.OeisA157237H1.a_eq_zero n hbound (hall n hmem)
