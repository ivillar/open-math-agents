import OMAStatements.S_mo_474009
import Mathlib

-- Problem: mo-474009, no integer polynomial f satisfies f(x) = (highest base-p digit of x)
-- mod p for all 0 <= x < p^n, when n > 1.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- For an integer polynomial, a - b divides f(a) - f(b). Take a = p^(n-1) and b = 0: p divides
-- a - b, so f(a) = f(b) mod p, but the highest digits are 1 and 0.

theorem OMA.solution : type_of% @OMA.S_mo_474009.main := by
  intro p n hp _ hn
  rintro ⟨f, hf⟩
  have hp1 : 1 < p := hp.one_lt
  have h0 := hf 0 (pow_pos hp.pos n)
  have hlt : p ^ (n - 1) < p ^ n := Nat.pow_lt_pow_right hp1 (by omega)
  have h1 := hf (p ^ (n - 1)) hlt
  have e0 : (0 : ℕ) / p ^ (n - 1) = 0 := Nat.zero_div _
  have e1 : p ^ (n - 1) / p ^ (n - 1) = 1 := Nat.div_self (pow_pos hp.pos _)
  rw [e0] at h0
  rw [e1] at h1
  have hdiv : ((p ^ (n - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) ∣
      f.eval ((p ^ (n - 1) : ℕ) : ℤ) - f.eval ((0 : ℕ) : ℤ) :=
    Polynomial.sub_dvd_eval_sub _ _ f
  have hpd : (p : ℤ) ∣ ((p ^ (n - 1) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) := by
    rw [Nat.cast_zero, sub_zero, Nat.cast_pow]
    exact dvd_pow_self _ (by omega)
  have h2 := dvd_trans hpd hdiv
  have h3 : f.eval ((0 : ℕ) : ℤ) ≡ f.eval ((p ^ (n - 1) : ℕ) : ℤ) [ZMOD (p : ℤ)] :=
    Int.modEq_iff_dvd.mpr h2
  have hfinal : ((0 : ℕ) : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD (p : ℤ)] :=
    h0.symm.trans (h3.trans h1)
  have h5 : (p : ℤ) ∣ ((1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) := Int.modEq_iff_dvd.mp hfinal
  rw [Nat.cast_zero, sub_zero] at h5
  have h6 : p ∣ 1 := Int.natCast_dvd_natCast.mp h5
  have h7 := Nat.le_of_dvd one_pos h6
  omega
