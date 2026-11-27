import OMAStatements.S_oeis_a249114
import Mathlib

/-!
# A249114: the minimum value of a(n) is 6

The first five triangular numbers are 1, 3, 6, 10, 15. For even n, n + 6 and n + 10 are even and
larger than 2; for odd n, n + 3 and n + 15 are. So at most three of n + T(1), ..., n + T(5) are
prime, and four primes need k ≥ 6. For n = 2 the values 3, 5, 17, 23 (j = 1, 2, 5, 6) are prime,
so a(2) = 6 (Jon Perry's observation in the entry).
-/

namespace PA249114
open OMA.S_oeis_a249114

theorem not_prime_even (m : ℕ) (h2 : 2 < m) (he : m % 2 = 0) : ¬ m.Prime := by
  intro hp
  have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 (Nat.dvd_of_mod_eq_zero he)).resolve_left (by norm_num)
  omega

theorem count_five (n : ℕ) (hn : 1 ≤ n) : primeCount n 5 ≤ 3 := by
  unfold primeCount
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · calc ((Finset.Icc 1 5).filter (fun j => (n + j * (j + 1) / 2).Prime)).card
        ≤ ({1, 2, 5} : Finset ℕ).card := by
          apply Finset.card_le_card
          intro j hj
          rw [Finset.mem_filter, Finset.mem_Icc] at hj
          obtain ⟨⟨hj1, hj5⟩, hp⟩ := hj
          interval_cases j
          · simp
          · simp
          · exact absurd hp (not_prime_even _ (by omega) (by omega))
          · exact absurd hp (not_prime_even _ (by omega) (by omega))
          · simp
      _ = 3 := by rfl
  · calc ((Finset.Icc 1 5).filter (fun j => (n + j * (j + 1) / 2).Prime)).card
        ≤ ({1, 3, 4} : Finset ℕ).card := by
          apply Finset.card_le_card
          intro j hj
          rw [Finset.mem_filter, Finset.mem_Icc] at hj
          obtain ⟨⟨hj1, hj5⟩, hp⟩ := hj
          interval_cases j
          · simp
          · exact absurd hp (not_prime_even _ (by omega) (by omega))
          · simp
          · simp
          · exact absurd hp (not_prime_even _ (by omega) (by omega))
      _ = 3 := by rfl

theorem mono (n k l : ℕ) (h : k ≤ l) : primeCount n k ≤ primeCount n l := by
  unfold primeCount
  apply Finset.card_le_card
  intro j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rintro ⟨⟨h1, h2⟩, hp⟩
  exact ⟨⟨h1, by omega⟩, hp⟩

theorem part1 (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 4 ≤ primeCount n k) : 6 ≤ k := by
  by_contra h
  have := (mono n k 5 (by omega)).trans (count_five n hn)
  omega

end PA249114

theorem OMA.solution : type_of% @OMA.S_oeis_a249114.main := by
  refine ⟨PA249114.part1, 2, by norm_num, ?_⟩
  have h6 : 4 ≤ OMA.S_oeis_a249114.primeCount 2 6 := by decide
  have hmem : 6 ∈ {k : ℕ | 0 < k ∧ 4 ≤ OMA.S_oeis_a249114.primeCount 2 k} := ⟨by norm_num, h6⟩
  unfold OMA.S_oeis_a249114.a
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨6, hmem⟩
  rintro k ⟨_, hk⟩
  exact PA249114.part1 2 (by norm_num) k hk
