import OMAStatements.S_oeis_a002966
import Mathlib

-- Problem: A002966, McNeil's conjecture that the second row T(2, m) of the Egyptian fraction array
-- equals A003167, the number of m-dimensional integral cuboids with volume equal to surface area.
-- Upstream: formal-conjectures statements/oeis-a002966.lean (declaration OMA.S_oeis_a002966.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjecture holds, by an elementary argument).
-- Proof: for positive x_i, sum_i prod_{j /= i} x_j = (prod x) (sum_i 1/x_i), so
-- prod x = 2 sum_i prod_{j /= i} x_j holds iff sum_i 1/x_i = 1/2. The two sets are equal.

namespace OMA.P_oeis_a002966

open OMA.S_oeis_a002966

theorem key (m : ℕ) (x : Fin m → ℕ) (hx : ∀ i, 0 < x i) :
    ((∏ i, x i : ℕ) = 2 * ∑ i, ∏ j ∈ Finset.univ.erase i, x j) ↔
      ∑ i, (1 : ℚ) / (x i : ℚ) = 1 / ((2 : ℕ) : ℚ) := by
  have hP : (∏ i, (x i : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by have := hx i; positivity)
  have hE : ∀ i, (∏ j ∈ Finset.univ.erase i, (x j : ℚ)) = (∏ j, (x j : ℚ)) / (x i : ℚ) := by
    intro i
    have hi : (x i : ℚ) ≠ 0 := by have := hx i; positivity
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (x j : ℚ)) (Finset.mem_univ i)]
    field_simp
  have hsum : (∑ i, ∏ j ∈ Finset.univ.erase i, (x j : ℚ))
      = (∏ j, (x j : ℚ)) * ∑ i, (1 : ℚ) / (x i : ℚ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hE i]
    ring
  have hcast : ((∏ i, x i : ℕ) = 2 * ∑ i, ∏ j ∈ Finset.univ.erase i, x j) ↔
      (∏ i, (x i : ℚ)) = 2 * ∑ i, ∏ j ∈ Finset.univ.erase i, (x j : ℚ) := by
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  rw [hcast, hsum]
  constructor
  · intro h
    have h2 : (∏ j, (x j : ℚ)) * (2 * ∑ i, (1 : ℚ) / (x i : ℚ) - 1) = 0 := by
      linear_combination (-1 : ℚ) * h
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact absurd h1 hP
    · push_cast
      linarith
  · intro h
    push_cast at h
    rw [h]
    ring

theorem main' : ∀ m : ℕ, 2 ≤ m → T 2 m = A003167 m := by
  intro m _
  unfold T A003167
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (key m x h2).mpr h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (key m x h2).mp h3⟩

end OMA.P_oeis_a002966

theorem OMA.solution : type_of% @OMA.S_oeis_a002966.main := OMA.P_oeis_a002966.main'
