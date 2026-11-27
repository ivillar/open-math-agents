import OMAStatements.S_mse_3767162
import Mathlib

-- Problem: mse-3767162, a natural number that is a sum of two rational squares is a sum of two
-- integer squares.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Clearing denominators gives n D^2 = A^2 + B^2 in the naturals. By the two-squares theorem
-- every prime q = 3 (mod 4) divides n D^2 to an even power, hence also n, since the valuations
-- differ by the even number 2 v_q(D). The two-squares theorem then gives n = x^2 + y^2.

theorem OMA.solution : type_of% @OMA.S_mse_3767162.main := by
  intro n hab
  obtain ⟨a, b, h⟩ := hab
  by_cases hn : n = 0
  · exact ⟨0, 0, by simp [hn]⟩
  obtain ⟨na, da, hda, ha⟩ : ∃ (na : ℤ) (da : ℕ), 0 < da ∧ a = (na : ℚ) / (da : ℚ) :=
    ⟨a.num, a.den, a.den_pos, (Rat.num_div_den a).symm⟩
  obtain ⟨nb, db, hdb, hb⟩ : ∃ (nb : ℤ) (db : ℕ), 0 < db ∧ b = (nb : ℚ) / (db : ℚ) :=
    ⟨b.num, b.den, b.den_pos, (Rat.num_div_den b).symm⟩
  subst ha hb
  have hda' : (da : ℚ) ≠ 0 := by positivity
  have hdb' : (db : ℚ) ≠ 0 := by positivity
  have h2 : (n : ℚ) * ((da : ℚ) * (db : ℚ)) ^ 2
      = ((na : ℚ) * (db : ℚ)) ^ 2 + ((nb : ℚ) * (da : ℚ)) ^ 2 := by
    rw [h]
    field_simp
  have h3 : (n : ℤ) * ((da : ℤ) * (db : ℤ)) ^ 2
      = (na * (db : ℤ)) ^ 2 + (nb * (da : ℤ)) ^ 2 := by
    exact_mod_cast h2
  have h4 : n * (da * db) ^ 2 = (na * (db : ℤ)).natAbs ^ 2 + (nb * (da : ℤ)).natAbs ^ 2 := by
    have h5 : ((n * (da * db) ^ 2 : ℕ) : ℤ)
        = (((na * (db : ℤ)).natAbs ^ 2 + (nb * (da : ℤ)).natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs, sq_abs]
      exact h3
    exact_mod_cast h5
  have hD : da * db ≠ 0 := Nat.mul_ne_zero hda.ne' hdb.ne'
  have hN := Nat.eq_sq_add_sq_iff.mp ⟨_, _, h4⟩
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
    apply Nat.eq_sq_add_sq_iff.mpr
    intro q hq hq3
    have hqp : q.Prime := (Nat.mem_primeFactors.mp hq).1
    have hfact : Fact q.Prime := ⟨hqp⟩
    have hmem : q ∈ (n * (da * db) ^ 2).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqp, Dvd.dvd.mul_right (Nat.mem_primeFactors.mp hq).2.1 _,
        Nat.mul_ne_zero hn (pow_ne_zero 2 hD)⟩
    have he := hN q hmem hq3
    have hpow : padicValNat q ((da * db) ^ 2)
        = padicValNat q (da * db) + padicValNat q (da * db) := by
      rw [pow_two, padicValNat.mul hD hD]
    rw [padicValNat.mul hn (pow_ne_zero 2 hD), hpow] at he
    exact (Nat.even_add.mp he).mpr ⟨_, rfl⟩
  exact ⟨x, y, by exact_mod_cast hxy⟩
