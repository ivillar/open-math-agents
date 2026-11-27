import OMAStatements.S_oeis_a061101
import Mathlib

/-!
# A061101: the squares with digital root 7

A positive square has digital root 7 exactly when it is ≡ 7 (mod 9), and x² ≡ 7 (mod 9) exactly when
x ≡ 4 or 5 (mod 9) (the residue check noted in the entry). So the terms are x_k² for the increasing
roots x_k = 9⌊k/2⌋ + 4 + (k mod 2), i.e. 4, 5, 13, 14, .... Two strictly increasing enumerations of
the same set coincide, so a(n) = x_(n−1)², which is ((9n − 8)/2)² for even n and ((9n − 1)/2)² for
odd n.
-/

namespace PA061101
open OMA.S_oeis_a061101

def root (k : ℕ) : ℕ := 9 * (k / 2) + 4 + k % 2

def g (k : ℕ) : ℕ := root k ^ 2

theorem root_lt (k : ℕ) : root k < root (k + 1) := by
  unfold root; omega

theorem g_mono : StrictMono g := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold g
  exact Nat.pow_lt_pow_left (root_lt k) (by norm_num)

theorem sq_mod9 (x : ℕ) : x ^ 2 % 9 = 7 ↔ (x % 9 = 4 ∨ x % 9 = 5) := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt x (show 9 > 0 by norm_num)
  interval_cases (x % 9) <;> simp

theorem dr_iff (m : ℕ) : digitalRoot m = 7 ↔ m % 9 = 7 := by
  unfold digitalRoot
  split_ifs with h
  · subst h; simp
  · constructor <;> intro hh <;> omega

theorem range_g : Set.range g = {m | IsSquare m ∧ digitalRoot m = 7} := by
  ext m
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨⟨root k, by unfold g; ring⟩, ?_⟩
    rw [dr_iff]
    unfold g
    exact (sq_mod9 _).mpr (by unfold root; omega)
  · rintro ⟨⟨r, rfl⟩, hd⟩
    rw [dr_iff, ← sq] at hd
    rcases (sq_mod9 r).mp hd with h | h
    · refine ⟨2 * (r / 9), ?_⟩
      unfold g root
      rw [← sq]
      congr 1
      omega
    · refine ⟨2 * (r / 9) + 1, ?_⟩
      unfold g root
      rw [← sq]
      congr 1
      omega

theorem nth_eq : Nat.nth (fun m => IsSquare m ∧ digitalRoot m = 7) = g := by
  have hinf : (Set.ofPred fun m => IsSquare m ∧ digitalRoot m = 7).Infinite := by
    have : Set.ofPred (fun m => IsSquare m ∧ digitalRoot m = 7) = Set.range g := by
      rw [range_g]
    rw [this]
    exact Set.infinite_range_of_injective g_mono.injective
  apply (StrictMono.range_inj (Nat.nth_strictMono hinf) g_mono).mp
  rw [Nat.range_nth_of_infinite hinf, range_g]

end PA061101

theorem OMA.solution : type_of% @OMA.S_oeis_a061101.main := by
  intro n hn
  unfold OMA.S_oeis_a061101.a
  rw [PA061101.nth_eq]
  unfold PA061101.g PA061101.root
  refine ⟨fun he => ?_, fun ho => ?_⟩
  · obtain ⟨m, rfl⟩ := he
    have hm : 1 ≤ m := by omega
    rw [show (m + m - 1) / 2 = m - 1 by omega, show (m + m - 1) % 2 = 1 by omega]
    push_cast [Nat.cast_sub hm]
    ring
  · obtain ⟨m, rfl⟩ := ho
    rw [show 2 * m + 1 - 1 = 2 * m by omega, show 2 * m / 2 = m by omega,
      show 2 * m % 2 = 0 by omega]
    push_cast
    ring
