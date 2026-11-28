import OMAStatements.S_oeis_a168019
import Mathlib

-- Problem: A168019, the number of partitions of n into parts divisible by k + 1 is p(n/(k+1)) if
-- k + 1 divides n and 0 otherwise.
-- Upstream: formal-conjectures statements/oeis-a168019.lean (declaration OMA.S_oeis_a168019.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (an elementary fact).
-- Proof: if all parts are divisible by d = k + 1 then so is their sum n. If n = d m, multiplying
-- the parts by d is a bijection from partitions of m onto partitions of n with all parts divisible
-- by d (the inverse divides every part by d).

namespace OMA.P_oeis_a168019

open OMA.S_oeis_a168019

def scale (d m : ℕ) (hd : 0 < d) (p : Nat.Partition m) : Nat.Partition (d * m) where
  parts := p.parts.map (fun i => d * i)
  parts_pos := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hi
    exact Nat.mul_pos hd (p.parts_pos hj)
  parts_sum := by
    rw [Multiset.sum_map_mul_left, Multiset.map_id', p.parts_sum]

theorem main' : ∀ n k : ℕ, A n k = if k + 1 ∣ n then Fintype.card (Nat.Partition (n / (k + 1))) else 0 := by
  intro n k
  unfold A
  have hd0 : 0 < k + 1 := by omega
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left m hd0]
    symm
    rw [← Finset.card_univ]
    apply Finset.card_bij (fun (p : Nat.Partition m) _ => scale (k + 1) m hd0 p)
    · intro p _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi
      obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hi
      exact dvd_mul_right _ _
    · intro p₁ _ p₂ _ hp
      have h1 : p₁.parts.map (fun i => (k + 1) * i) = p₂.parts.map (fun i => (k + 1) * i) := by
        have := congrArg Nat.Partition.parts hp
        simpa [scale] using this
      exact Nat.Partition.ext (Multiset.map_injective (mul_right_injective₀ (by omega)) h1)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hre : q.parts.map (fun i => (k + 1) * (i / (k + 1))) = q.parts := by
        conv_rhs => rw [← Multiset.map_id q.parts]
        apply Multiset.map_congr rfl
        intro i hi
        exact Nat.mul_div_cancel' (hq i hi)
      have hsum : (q.parts.map (fun i => i / (k + 1))).sum = m := by
        have h2 : (k + 1) * (q.parts.map (fun i => i / (k + 1))).sum = (k + 1) * m := by
          rw [← Multiset.sum_map_mul_left, hre, q.parts_sum]
        exact Nat.eq_of_mul_eq_mul_left hd0 h2
      refine ⟨⟨q.parts.map (fun i => i / (k + 1)), ?_, hsum⟩, Finset.mem_univ _, ?_⟩
      · intro j hj
        obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hj
        have hpos := q.parts_pos hi
        have hdvd := hq i hi
        exact Nat.div_pos (Nat.le_of_dvd hpos hdvd) hd0
      · apply Nat.Partition.ext
        simp only [scale, Multiset.map_map, Function.comp_def]
        exact hre
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    apply h
    rw [← p.parts_sum]
    exact Multiset.dvd_sum hp

end OMA.P_oeis_a168019

theorem OMA.solution : type_of% @OMA.S_oeis_a168019.main := OMA.P_oeis_a168019.main'
