import OMAStatements.S_oeis_a104934
import Mathlib

-- Problem: A104934, 2a(n) = A007482(n) + A007483(n-1).
-- Upstream: formal-conjectures statements/oeis-a104934.lean (declaration OMA.S_oeis_a104934.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here. Proof: all three sequences satisfy x(n+2) = 3x(n+1) + 2x(n), and the identity holds for n = 1, 2, so it propagates by induction.

namespace OMA.P_oeis_a104934

open OMA.S_oeis_a104934

theorem key : ∀ n : ℕ, 2 * a (n + 1) = b (n + 1) + c n ∧ 2 * a (n + 2) = b (n + 2) + c (n + 1)
  | 0 => by refine ⟨rfl, rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := key n
    refine ⟨h2, ?_⟩
    have ea : a (n + 3) = 3 * a (n + 2) + 2 * a (n + 1) := rfl
    have eb : b (n + 3) = 3 * b (n + 2) + 2 * b (n + 1) := rfl
    have ec : c (n + 2) = 3 * c (n + 1) + 2 * c n := rfl
    rw [show n + 1 + 2 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring, ea, eb, ec]
    omega

theorem main' : 2 * a 0 = b 0 + 1 ∧ ∀ n : ℕ, 1 ≤ n → 2 * a n = b n + c (n - 1) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact (key m).1

end OMA.P_oeis_a104934

theorem OMA.solution : type_of% @OMA.S_oeis_a104934.main := OMA.P_oeis_a104934.main'
