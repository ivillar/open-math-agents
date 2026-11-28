import OMAStatements.S_oeis_a100873
import Mathlib

/-!
Credit: @ivillar
Proof: let q = p + 2 be prime. In ZMod q, Fermat's little theorem gives p^q = p, and p = -2,
so p^q + 2 = p + 2 = 0, i.e. q divides p^q + 2.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a100873.main := by
  intro p _ hq
  have := Fact.mk hq
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.pow_card]
  have h := ZMod.natCast_self (p + 2)
  push_cast at h
  exact h
