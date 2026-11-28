import OMAStatements.S_oeis_a203510
import Mathlib

-- Problem: A203510, the superfactorial prod_{i=1}^{n-1} i! divides prod_{1<=j<k<=n} (k! + j!).
-- Upstream: formal-conjectures statements/oeis-a203510.lean (declaration OMA.S_oeis_a203510.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjecture holds, with an elementary proof). Proof: the factor k = n of
-- the product is prod_{j=1}^{n-1} (n! + j!), and j! divides n! + j! for each j < n, so this factor
-- alone is divisible by prod_{j=1}^{n-1} j!.

namespace OMA.P_oeis_a203510

open OMA.S_oeis_a203510

theorem main' : ∀ n : ℕ, 1 ≤ n → superfactorial (n - 1) ∣ A203482 n := by
  intro n hn
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    simp [superfactorial]
  · have hsf : superfactorial (n - 1) = ∏ j ∈ Finset.Ico 1 n, Nat.factorial j := by
      unfold superfactorial
      rw [show Finset.Icc 1 (n - 1) = Finset.Ico 1 n from by
        ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
    have h1 : ∏ j ∈ Finset.Ico 1 n, Nat.factorial j ∣
        ∏ j ∈ Finset.Ico 1 n, (Nat.factorial n + Nat.factorial j) := by
      apply Finset.prod_dvd_prod_of_dvd
      intro j hj
      simp only [Finset.mem_Ico] at hj
      exact Nat.dvd_add (Nat.factorial_dvd_factorial (by omega)) dvd_rfl
    have h2 : ∏ j ∈ Finset.Ico 1 n, (Nat.factorial n + Nat.factorial j) ∣ A203482 n := by
      unfold A203482
      exact Finset.dvd_prod_of_mem
        (fun k => ∏ j ∈ Finset.Ico 1 k, (Nat.factorial k + Nat.factorial j))
        (Finset.mem_Icc.mpr ⟨h, le_rfl⟩)
    rw [hsf]
    exact h1.trans h2

end OMA.P_oeis_a203510

theorem OMA.solution : type_of% @OMA.S_oeis_a203510.main := OMA.P_oeis_a203510.main'
