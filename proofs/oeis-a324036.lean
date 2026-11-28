import OMAStatements.S_oeis_a324036
import Mathlib

-- Problem: A324036, the recurrence a(n) = 2 a(n-4) - a(n-8) for n > 7.
-- Upstream: formal-conjectures statements/oeis-a324036.lean (declaration OMA.S_oeis_a324036.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated recurrence holds).
-- Proof: on each residue class mod 4 the explicit formula is linear in n, so its second
-- difference with step 4 vanishes; case analysis plus omega.

namespace OMA.P_oeis_a324036

open OMA.S_oeis_a324036

theorem main' : ∀ n : ℕ, 7 < n → (a n : ℤ) = 2 * (a (n - 4) : ℤ) - (a (n - 8) : ℤ) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 4 = m + 4 by omega, show m + 8 - 8 = m by omega]
  unfold a
  split_ifs <;> omega

end OMA.P_oeis_a324036

theorem OMA.solution : type_of% @OMA.S_oeis_a324036.main := OMA.P_oeis_a324036.main'
