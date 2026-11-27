import OMAStatements.S_oeis_a280523
import Mathlib

/-!
# A280523: Kagey's conjecture a(n) = A215004(2n − 2)

By simultaneous induction on k, b(2k) = F(2k+3) − (k+1) and b(2k+1) = F(2k+4) − (k+2): each step
uses b(m+2) = b(m+1) + b(m) + floor((m+2)/2) and F(j+2) = F(j) + F(j+1). With k = n − 1 the first
identity reads b(2n−2) = F(2n+1) − n = a(n) (Nathan Fox notes in the entry that the conjecture is
true).
-/

namespace PA280523
open OMA.S_oeis_a280523

theorem key (k : ℕ) :
    b (2 * k) = (Nat.fib (2 * k + 3) : ℤ) - (k + 1) ∧
      b (2 * k + 1) = (Nat.fib (2 * k + 4) : ℤ) - (k + 2) := by
  induction k with
  | zero => simp [b, Nat.fib_add_two]
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    have e0 : b (2 * (k + 1)) = b (2 * k + 1) + b (2 * k) + ((2 * k + 2) / 2 : ℕ) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring]; rfl
    have e1 : b (2 * (k + 1) + 1) = b (2 * (k + 1)) + b (2 * k + 1) + ((2 * k + 3) / 2 : ℕ) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      rfl
    have f0 : Nat.fib (2 * (k + 1) + 3) = Nat.fib (2 * k + 3) + Nat.fib (2 * k + 4) := by
      rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 2 by ring, Nat.fib_add_two]
    have f1 : Nat.fib (2 * (k + 1) + 4) = Nat.fib (2 * k + 4) + Nat.fib (2 * (k + 1) + 3) := by
      rw [show 2 * (k + 1) + 4 = (2 * k + 4) + 2 by ring, Nat.fib_add_two]
      congr 2
    rw [show (2 * k + 2) / 2 = k + 1 by omega] at e0
    rw [show (2 * k + 3) / 2 = k + 1 by omega] at e1
    refine ⟨?_, ?_⟩
    · rw [e0, h0, h1, f0]; push_cast; ring
    · rw [e1, e0, h0, h1, f1, f0]; push_cast; ring

end PA280523

theorem OMA.solution : type_of% @OMA.S_oeis_a280523.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (k + 1) - 2 = 2 * k by omega, (PA280523.key k).1]
  unfold OMA.S_oeis_a280523.a
  rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
  push_cast
  ring
