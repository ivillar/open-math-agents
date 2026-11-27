import OMAStatements.S_oeis_a140829
import Mathlib

/-!
Credit: @ivillar
Proof: write F = Nat.fib. For k >= 0, a(2k+9) = F(k+6) - 1 and a(2k+10) = F(k+5) + F(k+3) + 1.
This is shown by induction on k: with x = F(k+3), y = F(k+4), the addition formula gives
F(2k+11) = F(k+5)^2 + F(k+6)^2 and F(2k+12) = F(k+5) F(k+6) + F(k+6) F(k+7), and the two
ceilings reduce to inequalities that follow from Cassini's identity y^2 - xy - x^2 = 1 or -1
together with 2 <= x and 3 <= y < 2x. The recurrence for n >= 14 then follows from the Fibonacci
recurrence, and n = 13 is checked directly.
-/

namespace OMAA140829Helpers
open OMA.S_oeis_a140829

theorem a_succ (n : ℕ) : a (n + 1) = ⌈(Nat.fib (n + 1) : ℚ) / (a n : ℚ)⌉₊ := rfl

theorem ceil_eq (F A q : ℕ) (hA : 0 < A) (hq : 0 < q) (h1 : (q : ℤ) * A < F + A)
    (h2 : (F : ℤ) ≤ q * A) : ⌈(F : ℚ) / (A : ℚ)⌉₊ = q := by
  have hA' : (0 : ℚ) < A := by exact_mod_cast hA
  have h1' : (q : ℚ) * A < F + A := by exact_mod_cast h1
  have h2' : (F : ℚ) ≤ q * A := by exact_mod_cast h2
  rw [Nat.ceil_eq_iff (by omega)]
  constructor
  · rw [lt_div_iff₀ hA', Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_one]
    linarith
  · rw [div_le_iff₀ hA']
    exact h2'

theorem ceil_nat (F A : ℕ) (hA : 0 < A) (hF : 0 < F) :
    ⌈(F : ℚ) / (A : ℚ)⌉₊ = (F + A - 1) / A := by
  have hd : (F + A - 1) / A * A + (F + A - 1) % A = F + A - 1 := by
    rw [mul_comm]; exact Nat.div_add_mod _ _
  have hm := Nat.mod_lt (F + A - 1) hA
  have hq : 0 < (F + A - 1) / A := Nat.div_pos (by omega) hA
  apply ceil_eq F A _ hA hq
  · exact_mod_cast (show (F + A - 1) / A * A < F + A by omega)
  · exact_mod_cast (show F ≤ (F + A - 1) / A * A by omega)

/-- A computable copy of the sequence, used to evaluate the first terms. -/
def b : ℕ → ℕ
  | 0 => 1
  | n + 1 => (Nat.fib (n + 1) + b n - 1) / b n

theorem a_eq_b (n : ℕ) : a n = b n ∧ 0 < a n := by
  induction n with
  | zero => exact ⟨rfl, Nat.one_pos⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hF : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
    have e : a (n + 1) = (Nat.fib (n + 1) + a n - 1) / a n := by
      rw [a_succ, ceil_nat _ _ h2 hF]
    refine ⟨?_, ?_⟩
    · rw [e, h1]
      rfl
    · rw [e]
      exact Nat.div_pos (by omega) h2

theorem a_eq (n : ℕ) : a n = b n := (a_eq_b n).1

theorem cass (m : ℕ) :
    ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2 = 1) ∨
      ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2 = -1) := by
  induction m with
  | zero => left; norm_num
  | succ m ih =>
    have h : (Nat.fib (m + 1 + 1) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
      have e : Nat.fib (m + 1 + 1) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
      exact_mod_cast e
    rw [h]
    rcases ih with ih | ih
    · right
      linear_combination -ih
    · left
      linear_combination -ih

theorem closed (k : ℕ) :
    a (2 * k + 9) = Nat.fib (k + 6) - 1 ∧
      a (2 * k + 10) = Nat.fib (k + 5) + Nat.fib (k + 3) + 1 := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · show a 9 = Nat.fib 6 - 1
      rw [a_eq]
      decide
    · show a 10 = Nat.fib 5 + Nat.fib 3 + 1
      rw [a_eq]
      decide
  | succ k ih =>
    obtain ⟨_, h2⟩ := ih
    have e3 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have e4 : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) := Nat.fib_add_two
    have e5 : Nat.fib (k + 5) = Nat.fib (k + 3) + Nat.fib (k + 4) := Nat.fib_add_two
    have e6 : Nat.fib (k + 6) = Nat.fib (k + 4) + Nat.fib (k + 5) := Nat.fib_add_two
    have e7 : Nat.fib (k + 7) = Nat.fib (k + 5) + Nat.fib (k + 6) := Nat.fib_add_two
    have p1 : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
    have p2 : 0 < Nat.fib (k + 2) := Nat.fib_pos.mpr (by omega)
    have f11 : Nat.fib (2 * k + 11) =
        Nat.fib (k + 5) * Nat.fib (k + 5) + Nat.fib (k + 6) * Nat.fib (k + 6) := by
      rw [show 2 * k + 11 = (k + 5) + (k + 5) + 1 by ring]
      exact Nat.fib_add _ _
    have f12 : Nat.fib (2 * k + 12) =
        Nat.fib (k + 5) * Nat.fib (k + 6) + Nat.fib (k + 6) * Nat.fib (k + 7) := by
      rw [show 2 * k + 12 = (k + 5) + (k + 6) + 1 by ring]
      exact Nat.fib_add _ _
    have hc : ((Nat.fib (k + 4) : ℤ) ^ 2 - Nat.fib (k + 4) * Nat.fib (k + 3) -
        (Nat.fib (k + 3) : ℤ) ^ 2 = 1) ∨ ((Nat.fib (k + 4) : ℤ) ^ 2 -
        Nat.fib (k + 4) * Nat.fib (k + 3) - (Nat.fib (k + 3) : ℤ) ^ 2 = -1) := cass (k + 3)
    have E5 : (Nat.fib (k + 5) : ℤ) = Nat.fib (k + 3) + Nat.fib (k + 4) := by exact_mod_cast e5
    have E6' : (Nat.fib (k + 6) : ℤ) = Nat.fib (k + 4) + Nat.fib (k + 5) := by exact_mod_cast e6
    have E7' : (Nat.fib (k + 7) : ℤ) = Nat.fib (k + 5) + Nat.fib (k + 6) := by exact_mod_cast e7
    have E6 : (Nat.fib (k + 6) : ℤ) = Nat.fib (k + 3) + 2 * Nat.fib (k + 4) := by linarith
    have E7 : (Nat.fib (k + 7) : ℤ) = 2 * Nat.fib (k + 3) + 3 * Nat.fib (k + 4) := by linarith
    have b1 : (Nat.fib (k + 4) : ℤ) < 2 * Nat.fib (k + 3) := by
      exact_mod_cast (show Nat.fib (k + 4) < 2 * Nat.fib (k + 3) by omega)
    have b2 : (3 : ℤ) ≤ Nat.fib (k + 4) := by
      exact_mod_cast (show 3 ≤ Nat.fib (k + 4) by omega)
    have b3 : (2 : ℤ) ≤ Nat.fib (k + 3) := by
      exact_mod_cast (show 2 ≤ Nat.fib (k + 3) by omega)
    have s1 : a (2 * k + 11) = Nat.fib (k + 7) - 1 := by
      rw [show 2 * k + 11 = (2 * k + 10) + 1 by ring, a_succ, h2,
        show 2 * k + 10 + 1 = 2 * k + 11 by ring]
      apply ceil_eq
      · omega
      · omega
      · rw [Nat.cast_sub (show 1 ≤ Nat.fib (k + 7) by omega), f11]
        push_cast
        rw [E7, E5, E6]
        rcases hc with hc | hc <;> linarith
      · rw [Nat.cast_sub (show 1 ≤ Nat.fib (k + 7) by omega), f11]
        push_cast
        rw [E7, E5, E6]
        rcases hc with hc | hc <;> linarith
    have s2 : a (2 * k + 12) = Nat.fib (k + 6) + Nat.fib (k + 4) + 1 := by
      rw [show 2 * k + 12 = (2 * k + 11) + 1 by ring, a_succ, s1,
        show 2 * k + 11 + 1 = 2 * k + 12 by ring]
      apply ceil_eq
      · omega
      · omega
      · rw [Nat.cast_sub (show 1 ≤ Nat.fib (k + 7) by omega), f12]
        push_cast
        rw [E7, E5, E6]
        rcases hc with hc | hc <;> linarith
      · rw [Nat.cast_sub (show 1 ≤ Nat.fib (k + 7) by omega), f12]
        push_cast
        rw [E7, E5, E6]
        rcases hc with hc | hc <;> linarith
    refine ⟨?_, ?_⟩
    · rw [show 2 * (k + 1) + 9 = 2 * k + 11 by ring, show k + 1 + 6 = k + 7 by ring]
      exact s1
    · rw [show 2 * (k + 1) + 10 = 2 * k + 12 by ring, show k + 1 + 5 = k + 6 by ring,
        show k + 1 + 3 = k + 4 by ring]
      exact s2

theorem closedZ (k : ℕ) :
    (a (2 * k + 9) : ℤ) = Nat.fib (k + 6) - 1 ∧
      (a (2 * k + 10) : ℤ) = Nat.fib (k + 5) + Nat.fib (k + 3) + 1 := by
  obtain ⟨h1, h2⟩ := closed k
  have p : 0 < Nat.fib (k + 6) := Nat.fib_pos.mpr (by omega)
  refine ⟨?_, ?_⟩
  · rw [h1, Nat.cast_sub (show 1 ≤ Nat.fib (k + 6) by omega), Nat.cast_one]
  · rw [h2]
    push_cast
    ring

theorem rec_even (k : ℕ) :
    (a (2 * k + 14) : ℤ) = -a (2 * k + 13) + a (2 * k + 12) + a (2 * k + 11) +
      a (2 * k + 10) + a (2 * k + 9) := by
  obtain ⟨c0a, c0b⟩ := closedZ k
  obtain ⟨c1a, c1b⟩ := closedZ (k + 1)
  obtain ⟨c2a, c2b⟩ := closedZ (k + 2)
  rw [show 2 * (k + 1) + 9 = 2 * k + 11 by ring, show k + 1 + 6 = k + 7 by ring] at c1a
  rw [show 2 * (k + 1) + 10 = 2 * k + 12 by ring, show k + 1 + 5 = k + 6 by ring,
    show k + 1 + 3 = k + 4 by ring] at c1b
  rw [show 2 * (k + 2) + 9 = 2 * k + 13 by ring, show k + 2 + 6 = k + 8 by ring] at c2a
  rw [show 2 * (k + 2) + 10 = 2 * k + 14 by ring, show k + 2 + 5 = k + 7 by ring,
    show k + 2 + 3 = k + 5 by ring] at c2b
  have e5 : Nat.fib (k + 5) = Nat.fib (k + 3) + Nat.fib (k + 4) := Nat.fib_add_two
  have e6 : Nat.fib (k + 6) = Nat.fib (k + 4) + Nat.fib (k + 5) := Nat.fib_add_two
  have e7 : Nat.fib (k + 7) = Nat.fib (k + 5) + Nat.fib (k + 6) := Nat.fib_add_two
  have e8 : Nat.fib (k + 8) = Nat.fib (k + 6) + Nat.fib (k + 7) := Nat.fib_add_two
  have E5 : (Nat.fib (k + 5) : ℤ) = Nat.fib (k + 3) + Nat.fib (k + 4) := by exact_mod_cast e5
  have E6 : (Nat.fib (k + 6) : ℤ) = Nat.fib (k + 4) + Nat.fib (k + 5) := by exact_mod_cast e6
  have E7 : (Nat.fib (k + 7) : ℤ) = Nat.fib (k + 5) + Nat.fib (k + 6) := by exact_mod_cast e7
  have E8 : (Nat.fib (k + 8) : ℤ) = Nat.fib (k + 6) + Nat.fib (k + 7) := by exact_mod_cast e8
  rw [c0a, c0b, c1a, c1b, c2a, c2b]
  linarith

theorem rec_odd (k : ℕ) :
    (a (2 * k + 15) : ℤ) = -a (2 * k + 14) + a (2 * k + 13) + a (2 * k + 12) +
      a (2 * k + 11) + a (2 * k + 10) := by
  obtain ⟨_, c0b⟩ := closedZ k
  obtain ⟨c1a, c1b⟩ := closedZ (k + 1)
  obtain ⟨c2a, c2b⟩ := closedZ (k + 2)
  obtain ⟨c3a, _⟩ := closedZ (k + 3)
  rw [show 2 * (k + 1) + 9 = 2 * k + 11 by ring, show k + 1 + 6 = k + 7 by ring] at c1a
  rw [show 2 * (k + 1) + 10 = 2 * k + 12 by ring, show k + 1 + 5 = k + 6 by ring,
    show k + 1 + 3 = k + 4 by ring] at c1b
  rw [show 2 * (k + 2) + 9 = 2 * k + 13 by ring, show k + 2 + 6 = k + 8 by ring] at c2a
  rw [show 2 * (k + 2) + 10 = 2 * k + 14 by ring, show k + 2 + 5 = k + 7 by ring,
    show k + 2 + 3 = k + 5 by ring] at c2b
  rw [show 2 * (k + 3) + 9 = 2 * k + 15 by ring, show k + 3 + 6 = k + 9 by ring] at c3a
  have e5 : Nat.fib (k + 5) = Nat.fib (k + 3) + Nat.fib (k + 4) := Nat.fib_add_two
  have e6 : Nat.fib (k + 6) = Nat.fib (k + 4) + Nat.fib (k + 5) := Nat.fib_add_two
  have e7 : Nat.fib (k + 7) = Nat.fib (k + 5) + Nat.fib (k + 6) := Nat.fib_add_two
  have e8 : Nat.fib (k + 8) = Nat.fib (k + 6) + Nat.fib (k + 7) := Nat.fib_add_two
  have e9 : Nat.fib (k + 9) = Nat.fib (k + 7) + Nat.fib (k + 8) := Nat.fib_add_two
  have E5 : (Nat.fib (k + 5) : ℤ) = Nat.fib (k + 3) + Nat.fib (k + 4) := by exact_mod_cast e5
  have E6 : (Nat.fib (k + 6) : ℤ) = Nat.fib (k + 4) + Nat.fib (k + 5) := by exact_mod_cast e6
  have E7 : (Nat.fib (k + 7) : ℤ) = Nat.fib (k + 5) + Nat.fib (k + 6) := by exact_mod_cast e7
  have E8 : (Nat.fib (k + 8) : ℤ) = Nat.fib (k + 6) + Nat.fib (k + 7) := by exact_mod_cast e8
  have E9 : (Nat.fib (k + 9) : ℤ) = Nat.fib (k + 7) + Nat.fib (k + 8) := by exact_mod_cast e9
  rw [c0b, c1a, c1b, c2a, c2b, c3a]
  linarith

end OMAA140829Helpers

open OMAA140829Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a140829.main := by
  intro n hn
  rcases Nat.lt_or_ge n 14 with h | h
  · obtain rfl : n = 13 := by omega
    simp only [a_eq]
    decide
  · obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 14 ∨ n = 2 * k + 15 :=
      ⟨(n - 14) / 2, by omega⟩
    · rw [show 2 * k + 14 - 1 = 2 * k + 13 by omega, show 2 * k + 14 - 2 = 2 * k + 12 by omega,
        show 2 * k + 14 - 3 = 2 * k + 11 by omega, show 2 * k + 14 - 4 = 2 * k + 10 by omega,
        show 2 * k + 14 - 5 = 2 * k + 9 by omega]
      exact rec_even k
    · rw [show 2 * k + 15 - 1 = 2 * k + 14 by omega, show 2 * k + 15 - 2 = 2 * k + 13 by omega,
        show 2 * k + 15 - 3 = 2 * k + 12 by omega, show 2 * k + 15 - 4 = 2 * k + 11 by omega,
        show 2 * k + 15 - 5 = 2 * k + 10 by omega]
      exact rec_odd k
