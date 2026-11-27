import OMAStatements.S_oeis_a143727
import Mathlib

/-!
# A143727: all terms are multiples of 15

If n ≢ 0 (mod 3) then one of n − 2, n + 2 is a multiple of 3 larger than 3; if n ≢ 0 (mod 5) then
one of n − 4, n + 4, n + 8, n + 2 is a multiple of 5 larger than 5 (n ≥ 10 because n − 8 is prime).
Either way one of the six numbers is composite (the residue check noted in the entry).
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a143727.main := by
  rintro n ⟨h1, h2, h3, h4, h5, h6⟩
  have hn : 10 ≤ n := by have := h5.two_le; omega
  have key : ∀ q d : ℕ, q.Prime → d ∣ q → 2 ≤ d → d = q := fun q d hq hd h2 =>
    ((Nat.Prime.eq_one_or_self_of_dvd hq d hd).resolve_left (by omega))
  have h3d : n % 3 = 0 := by
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · exact h
    · have := key _ 3 h2 (by omega) (by norm_num); omega
    · have := key _ 3 h1 (by omega) (by norm_num); omega
  have h5d : n % 5 = 0 := by
    rcases (by omega : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4) with h | h | h | h | h
    · exact h
    · have := key _ 5 h4 (by omega) (by norm_num); omega
    · have := key _ 5 h6 (by omega) (by norm_num); omega
    · have := key _ 5 h2 (by omega) (by norm_num); omega
    · have := key _ 5 h3 (by omega) (by norm_num); omega
  omega
