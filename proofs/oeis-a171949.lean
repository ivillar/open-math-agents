import OMAStatements.S_oeis_a171949
import Mathlib

/-!
Credit: @ivillar
Proof: write v(n) for the exponent of 2 in n. By strong induction, n is a P-position exactly
when n = 0 or (n > 0 and v(n) mod 4 is 2 or 3).
* If v(n) mod 4 is 2 or 3, then n = 4q with v(q) mod 4 equal to 0 or 1, so the move to q leads
  to an N-position, and n - 1, n - 3 (odd) and n - 2 (with v = 1) are positive N-positions.
* Otherwise, with q = floor(n/4): if 4 does not divide n, one of the moves to 4q = n - (n mod 4)
  or to q reaches a P-position, since v(4q) = v(q) + 2 (or 4q = 0); if 4 divides n, then v(q)
  mod 4 is 2 or 3 and the move to q = n/4 reaches a P-position.
So the P-positions are 0 followed by the elements of the second set in increasing order, and
the k-th positive P-position is the k-th element of that set (the counts differ by one).
-/

namespace OMAA171949Helpers
open OMA.S_oeis_a171949

theorem v_odd (n : ℕ) (h : n % 2 = 1) : n.factorization 2 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (by omega)

theorem v_two (n : ℕ) (h : n % 4 = 2) : n.factorization 2 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  have hm : m ≠ 0 := by omega
  rw [Nat.factorization_mul two_ne_zero hm, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, v_odd m (by omega)]

theorem v_four (q : ℕ) (hq : q ≠ 0) : (4 * q).factorization 2 = q.factorization 2 + 2 := by
  rw [Nat.factorization_mul (by norm_num) hq, Finsupp.add_apply,
    show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same]
  ring

theorem key (n : ℕ) : losing n ↔ n = 0 ∨ trailing n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [losing]
  constructor
  · intro hl
    by_contra hc
    have hn : n ≠ 0 := fun h => hc (Or.inl h)
    have ht : ¬ (2 ≤ n.factorization 2 % 4) := fun h => hc (Or.inr ⟨by omega, h⟩)
    have win : ∃ m, m < n ∧ (n ≤ m + 3 ∨ m = n / 4) ∧ (m = 0 ∨ trailing m) := by
      rcases Nat.eq_zero_or_pos (n % 4) with hr | hr
      · obtain ⟨q, rfl⟩ : ∃ q, n = 4 * q := ⟨n / 4, by omega⟩
        have hq : q ≠ 0 := by omega
        rw [v_four q hq] at ht
        refine ⟨q, by omega, Or.inr (by omega), Or.inr ⟨by omega, by omega⟩⟩
      · by_cases hq : n / 4 = 0
        · exact ⟨0, by omega, Or.inl (by omega), Or.inl rfl⟩
        · by_cases hv : 2 ≤ (n / 4).factorization 2 % 4
          · exact ⟨n / 4, by omega, Or.inr rfl, Or.inr ⟨by omega, hv⟩⟩
          · refine ⟨4 * (n / 4), by omega, Or.inl (by omega), Or.inr ⟨by omega, ?_⟩⟩
            rw [v_four (n / 4) hq]
            omega
    obtain ⟨m, hm, hmove, hlm⟩ := win
    exact hl m hm hmove ((ih m hm).mpr hlm)
  · rintro (rfl | ⟨hpos, hv⟩) m hm hmove hlm
    · omega
    · rw [ih m hm] at hlm
      have h4 : 4 ∣ n := by
        have := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : n ≠ 0)).mpr
          (show 2 ≤ n.factorization 2 by omega)
        simpa using this
      obtain ⟨q, rfl⟩ := h4
      have hq : q ≠ 0 := by omega
      rw [v_four q hq] at hv
      rcases hmove with hmove | hmove
      · have hcases : m = 4 * q - 1 ∨ m = 4 * q - 2 ∨ m = 4 * q - 3 := by omega
        rcases hlm with hlm | ⟨_, hlm⟩
        · omega
        · rcases hcases with rfl | rfl | rfl
          · rw [v_odd _ (by omega)] at hlm
            omega
          · rw [v_two _ (by omega)] at hlm
            omega
          · rw [v_odd _ (by omega)] at hlm
            omega
      · rw [show 4 * q / 4 = q by omega] at hmove
        subst hmove
        rcases hlm with hlm | ⟨_, hlm⟩
        · omega
        · omega

theorem trailing_infinite : {n | trailing n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨2 ^ (4 * N + 2), ⟨by positivity, ?_⟩, ?_⟩
  · rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    omega
  · calc N < 2 ^ N := Nat.lt_two_pow_self
      _ ≤ 2 ^ (4 * N + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

end OMAA171949Helpers

open OMAA171949Helpers OMA.S_oeis_a171949 in
theorem OMA.solution : type_of% @OMA.S_oeis_a171949.main := by
  classical
  intro k
  have hL : losing = fun n => n = 0 ∨ trailing n := by
    funext n
    exact propext (key n)
  rw [hL]
  set t := Nat.nth trailing k with ht
  have pt : trailing t := Nat.nth_mem_of_infinite trailing_infinite k
  have ct : Nat.count trailing t = k := Nat.count_nth_of_infinite trailing_infinite k
  obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by have := pt.1; omega⟩
  have hc : Nat.count (fun n => n = 0 ∨ trailing n) t = k + 1 := by
    rw [← ct, hs, Nat.count_succ', Nat.count_succ']
    have h0 : ¬ trailing 0 := fun h => by have := h.1; omega
    have hsame : (fun n => n + 1 = 0 ∨ trailing (n + 1)) = fun n => trailing (n + 1) := by
      funext n
      apply propext
      constructor
      · rintro (h | h)
        · omega
        · exact h
      · exact Or.inr
    simp only [hsame, h0, if_true, if_false, true_or]
  rw [← hc]
  exact Nat.nth_count (p := fun n => n = 0 ∨ trailing n) (Or.inr pt)
