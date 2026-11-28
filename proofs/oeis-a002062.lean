import OMAStatements.S_oeis_a002062
import Mathlib

-- Problem: A002062, a(n) = Fibonacci(n) + n; Dement's identity a(n+2) = A006355(n+4) - A066982(n+1).
-- Upstream: formal-conjectures statements/oeis-a002062.lean (declaration OMA.S_oeis_a002062.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here. Proof: L(n+1) = F(n) + F(n+2), so the right side is 2F(n+3) - F(n+1) - F(n+3) + n + 2 = F(n+2) + n + 2.

namespace OMA.P_oeis_a002062

open OMA.S_oeis_a002062

theorem lucas_eq : ∀ n : ℕ, (lucas (n + 1) : ℤ) = Nat.fib n + Nat.fib (n + 2)
  | 0 => by simp [lucas]
  | 1 => by simp [lucas, Nat.fib_add_two]
  | n + 2 => by
    have h1 := lucas_eq n
    have h2 := lucas_eq (n + 1)
    have e : lucas (n + 2 + 1) = lucas (n + 2) + lucas (n + 1) := rfl
    rw [e]
    push_cast
    rw [h1, h2]
    have f1 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    have f2 : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      rw [show n + 3 = (n + 1) + 2 by ring, Nat.fib_add_two]; push_cast; ring
    have f3 : (Nat.fib (n + 2 + 2) : ℤ) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [show n + 1 + 2 = n + 3 by ring, f3, f2, f1]
    ring

theorem main' : ∀ n : ℕ,
    (A002062 (n + 2) : ℤ) = (A006355 (n + 4) : ℤ) - A066982 (n + 1) := by
  intro n
  unfold A002062 A066982
  rw [show n + 1 + 1 = (n + 1) + 1 by ring, lucas_eq (n + 1)]
  have e : A006355 (n + 4) = 2 * Nat.fib (n + 3) := rfl
  rw [e]
  have f1 : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
    rw [show n + 3 = (n + 1) + 2 by ring, Nat.fib_add_two]; push_cast; ring
  push_cast
  rw [show n + 1 + 2 = n + 3 by ring, f1]
  ring

end OMA.P_oeis_a002062

theorem OMA.solution : type_of% @OMA.S_oeis_a002062.main := OMA.P_oeis_a002062.main'
