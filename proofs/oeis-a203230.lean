import OMAStatements.S_oeis_a203230
import Mathlib

/-!
# A203230: Mathar's recurrence and generating function

The digits repeat with period L, so any L consecutive digits have the same product P and the same
(L−1)-st elementary symmetric function c. Hence (p, e) = products n satisfies p(n+L) = P·p(n) and
e(n+L) = P·e(n) + c·p(n), and eliminating p gives e(n+2L) = 2P·e(n+L) − P²·e(n). Multiplying the
series by (1 − Px^L)² kills every coefficient from x^(2L) on; the first 2L are computed directly.
-/

namespace PA203230
open OMA.S_oeis_a203230

theorem step (n : ℕ) :
    products (n + 1) = ((products n).1 * digit n, (products n).2 * digit n + (products n).1) := by
  rw [products]

theorem window (n : ℕ) :
    digit n * digit (n + 1) = 3 ∧
    digit (n + 1) +
      digit n = 4 := by
  have h := Nat.mod_lt n (show 2 > 0 by norm_num)
  have e1 : (n + 1) % 2 = (n % 2 + 1) % 2 := by omega
  unfold digit
  rw [e1]
  interval_cases (n % 2) <;> norm_num

theorem period (n : ℕ) :
    (products (n + 2)).1 = 3 * (products n).1 ∧
    (products (n + 2)).2 = 3 * (products n).2 + 4 * (products n).1 := by
  obtain ⟨h1, h2⟩ := window n
  simp only [step]
  constructor
  · linear_combination (products n).1 * h1
  · linear_combination (products n).2 * h1 + (products n).1 * h2

theorem rec (m : ℕ) : a (m + 4) = 6 * a (m + 2) - 9 * a m := by
  obtain ⟨p1, e1⟩ := period m
  obtain ⟨p2, e2⟩ := period (m + 2)
  unfold a
  rw [show m + 4 = m + 2 + 2 by ring, e2, e1, p1]
  ring

end PA203230

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a203230.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [PA203230.rec m, show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega]
  · ext n
    have hexp : ((1 - C 3 * X ^ 2 : ℤ⟦X⟧)) ^ 2 * mk OMA.S_oeis_a203230.a =
        mk OMA.S_oeis_a203230.a - C 6 * (X ^ 2 * mk OMA.S_oeis_a203230.a) +
          C 9 * (X ^ 4 * mk OMA.S_oeis_a203230.a) := by
      have hA : (C 6 : ℤ⟦X⟧) = 2 * C 3 := by
        rw [show (6 : ℤ) = 2 * 3 by norm_num, map_mul]; rfl
      have hB : (C 9 : ℤ⟦X⟧) = C 3 * C 3 := by rw [← map_mul]; norm_num
      rw [hA, hB]
      ring
    rw [hexp]
    simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      rw [if_pos (by omega), if_pos (by omega), show m + 4 - 2 = m + 2 by omega,
        show m + 4 - 4 = m by omega, PA203230.rec m]
      simp
