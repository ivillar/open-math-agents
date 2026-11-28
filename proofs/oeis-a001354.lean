import OMAStatements.S_oeis_a001354
import Mathlib

-- Problem: A001354, coordination sequence of the 3^7 tessellation and Fibonacci numbers.
-- Upstream: formal-conjectures statements/oeis-a001354.lean (declaration OMA.S_oeis_a001354.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here. Proof: the even-index Fibonacci numbers satisfy F(2k+4) = 3F(2k+2) - F(2k),
-- the recurrence of the coordination sequence, so c(k) = 7F(2k) for k >= 1 by induction; the
-- second identity is F(2k+2) = F(2k) + F(2k+1).

namespace OMA.P_oeis_a001354

open OMA.S_oeis_a001354

theorem fib_step (k : ℕ) : (Nat.fib (2 * k + 4) : ℤ) = 3 * Nat.fib (2 * k + 2) - Nat.fib (2 * k) := by
  have h1 : (Nat.fib (2 * k + 2) : ℤ) = Nat.fib (2 * k) + Nat.fib (2 * k + 1) := by
    rw [Nat.fib_add_two]; push_cast; ring
  have h2 : (Nat.fib (2 * k + 3) : ℤ) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := by
    rw [show 2 * k + 3 = (2 * k + 1) + 2 by ring, Nat.fib_add_two]; push_cast; ring
  have h3 : (Nat.fib (2 * k + 4) : ℤ) = Nat.fib (2 * k + 2) + Nat.fib (2 * k + 3) := by
    rw [show 2 * k + 4 = (2 * k + 2) + 2 by ring, Nat.fib_add_two]; push_cast; ring
  rw [h3, h2, h1]
  ring

theorem coord_pair : ∀ k : ℕ, (coordination (k + 1) : ℤ) = 7 * Nat.fib (2 * k + 2) ∧
    (coordination (k + 2) : ℤ) = 7 * Nat.fib (2 * k + 4)
  | 0 => ⟨rfl, rfl⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := coord_pair k
    refine ⟨by rw [show k + 1 + 1 = k + 2 by ring, h2]; ring_nf, ?_⟩
    have e : coordination (k + 1 + 2) = 3 * coordination (k + 2) - coordination (k + 1) := rfl
    have hle : coordination (k + 1) ≤ 3 * coordination (k + 2) := by
      have hm : Nat.fib (2 * k + 2) ≤ Nat.fib (2 * k + 4) := Nat.fib_mono (by omega)
      have : (coordination (k + 1) : ℤ) ≤ 3 * (coordination (k + 2) : ℤ) := by
        rw [h1, h2]
        have : (Nat.fib (2 * k + 2) : ℤ) ≤ Nat.fib (2 * k + 4) := by exact_mod_cast hm
        have h0 : (0 : ℤ) ≤ Nat.fib (2 * k + 4) := by positivity
        linarith
      exact_mod_cast this
    rw [e, Nat.cast_sub hle]
    push_cast
    rw [h1, h2, fib_step (k + 1), show 2 * (k + 1) + 2 = 2 * k + 4 by ring,
      show 2 * (k + 1) = 2 * k + 2 by ring]
    ring

theorem main' : ∀ k : ℕ, 1 < k →
      coordination k = 7 * Nat.fib (2 * k) ∧
        coordination (k + 1) = coordination k + 7 * Nat.fib (2 * k + 1) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h1 := (coord_pair j).2
  have h2 := (coord_pair (j + 1)).2
  rw [show j + 1 + 2 = j + 2 + 1 by ring, show 2 * (j + 1) + 4 = 2 * (j + 2) + 2 by ring] at h2
  rw [show 2 * j + 4 = 2 * (j + 2) by ring] at h1
  have f : (Nat.fib (2 * (j + 2) + 2) : ℤ) = Nat.fib (2 * (j + 2)) + Nat.fib (2 * (j + 2) + 1) := by
    rw [Nat.fib_add_two]; push_cast; ring
  constructor
  · exact_mod_cast h1
  · have : (coordination (j + 2 + 1) : ℤ) = coordination (j + 2) + 7 * Nat.fib (2 * (j + 2) + 1) := by
      rw [h2, h1, f]; ring
    exact_mod_cast this

end OMA.P_oeis_a001354

theorem OMA.solution : type_of% @OMA.S_oeis_a001354.main := OMA.P_oeis_a001354.main'
