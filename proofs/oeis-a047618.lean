import OMAStatements.S_oeis_a047618
import Mathlib

-- Problem: A047618, numbers congruent to {0, 2, 5} mod 8.
-- Upstream: formal-conjectures statements/oeis-a047618.lean (declaration OMA.S_oeis_a047618.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: the (m+1)-st term is 8 (m / 3) + [0, 2, 5] (m mod 3); both identities are then
-- checked residue by residue.

namespace OMA.P_oeis_a047618

open OMA.S_oeis_a047618

/-- The residues in increasing order. -/
def B (r : ℕ) : ℕ := if r = 0 then 0 else if r = 1 then 2 else 5

/-- The claimed enumeration (zero-based). -/
def f (m : ℕ) : ℕ := 8 * (m / 3) + B (m % 3)

theorem f_mono : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro m
  unfold f B
  split_ifs <;> omega

theorem f_maps (m : ℕ) : InSeq (f m) := by
  unfold InSeq f B
  split_ifs <;> omega

theorem f_surj (k : ℕ) (hk : InSeq k) : ∃ m, f m = k := by
  unfold InSeq at hk
  rcases hk with h | h | h
  · exact ⟨3 * (k / 8), by unfold f B; split_ifs <;> omega⟩
  · exact ⟨3 * (k / 8) + 1, by unfold f B; split_ifs <;> omega⟩
  · exact ⟨3 * (k / 8) + 2, by unfold f B; split_ifs <;> omega⟩

theorem nth_eq (m : ℕ) : Nat.nth InSeq m = f m := by
  have hinf : (Set.ofPred InSeq).Infinite :=
    Set.infinite_of_injective_forall_mem f_mono.injective f_maps
  have hU : ∀ k, k ∈ {k : ℕ | ∀ hf : (Set.ofPred InSeq).Finite, k < hf.toFinset.card} :=
    fun k hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f ?_ ?_ ?_ (hU m)).symm
  · intro x hx
    obtain ⟨k, hk⟩ := f_surj x hx
    exact ⟨k, hU k, hk⟩
  · intro k _
    exact f_maps k
  · exact f_mono.strictMonoOn _

theorem a_eq (n : ℕ) : a n = f (n - 1) := nth_eq (n - 1)

theorem part1 : ∀ n : ℕ, 1 ≤ n → (a n : ℤ) + a (n + 1) + a (n + 2) = 8 * (n : ℤ) - 1 := by
  intro n hn
  rw [a_eq, a_eq, a_eq]
  unfold f B
  split_ifs <;> omega

theorem part2 : a 1 = 0 ∧ a 2 = 2 ∧ a 3 = 5 ∧
    ∀ n : ℕ, 3 < n → (a n : ℤ) = 8 * ((n : ℤ) - 2) - a (n - 1) - a (n - 2) - 1 := by
  refine ⟨by rw [a_eq]; rfl, by rw [a_eq]; rfl, by rw [a_eq]; rfl, ?_⟩
  intro n hn
  rw [a_eq, a_eq, a_eq]
  unfold f B
  split_ifs <;> omega

end OMA.P_oeis_a047618

theorem OMA.solution : type_of% @OMA.S_oeis_a047618.main :=
  ⟨OMA.P_oeis_a047618.part1, OMA.P_oeis_a047618.part2⟩
