import OMAStatements.S_mo_488704
import Mathlib

-- Problem: mo-488704, the conjectured pattern for solvability of phi(x) = phi(a x + b).
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- The last claim of the pattern (no solutions for a >= 6) fails: x = 72990721 is prime, so
-- phi(x) = 72990720, and 6 x + 8241414 = 446185740 = 4 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 has
-- phi = 2 * 2 * 4 * 6 * 10 * 12 * 16 * 18 * 22 = 72990720 as well. So (a, b) = (6, 8241414)
-- has a solution.

namespace MO488704

theorem step (m p t : ℕ) (hp : p.Prime) (h : Nat.Coprime m p) (ht : Nat.totient m = t) :
    Nat.totient (m * p) = t * (p - 1) := by
  rw [Nat.totient_mul h, ht, Nat.totient_prime hp]

theorem t12 : Nat.totient 12 = 4 := by decide +kernel

theorem t60 : Nat.totient 60 = 16 := by
  have h := step 12 5 4 (by norm_num) (by norm_num) t12
  norm_num at h
  exact h

theorem t420 : Nat.totient 420 = 96 := by
  have h := step 60 7 16 (by norm_num) (by norm_num) t60
  norm_num at h
  exact h

theorem t4620 : Nat.totient 4620 = 960 := by
  have h := step 420 11 96 (by norm_num) (by norm_num) t420
  norm_num at h
  exact h

theorem t60060 : Nat.totient 60060 = 11520 := by
  have h := step 4620 13 960 (by norm_num) (by norm_num) t4620
  norm_num at h
  exact h

theorem t1021020 : Nat.totient 1021020 = 184320 := by
  have h := step 60060 17 11520 (by norm_num) (by norm_num) t60060
  norm_num at h
  exact h

theorem t19399380 : Nat.totient 19399380 = 3317760 := by
  have h := step 1021020 19 184320 (by norm_num) (by norm_num) t1021020
  norm_num at h
  exact h

theorem tbig : Nat.totient 446185740 = 72990720 := by
  have h := step 19399380 23 3317760 (by norm_num) (by norm_num) t19399380
  norm_num at h
  exact h

theorem prime_x : Nat.Prime 72990721 := by norm_num

theorem tx : Nat.totient 72990721 = 72990720 := Nat.totient_prime prime_x

end MO488704

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_488704.main) := by
  rintro ⟨-, -, -, -, -, h⟩
  apply h 6 8241414 (le_refl 6)
  refine ⟨72990721, by norm_num, ?_⟩
  have e : 6 * 72990721 + 8241414 = 446185740 := by norm_num
  rw [e, MO488704.tx, MO488704.tbig]
