import OMAStatements.S_mo_302974
import Mathlib

-- Problem: mo-302974, for every prime p there is a commutative ring R whose ring of Witt
-- vectors W(R) has nonzero p-torsion.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Take R = F_p[e] / (e^2), the dual numbers over F_p, a ring of characteristic p. In
-- characteristic p one has p * x = V (F x), and F is the coefficientwise p-th power map. The
-- Teichmuller lift x = [e] is nonzero (its 0-th coefficient is e), and F [e] = [e^p] = [0] = 0
-- because e^2 = 0 and p >= 2. Hence p * [e] = 0.

theorem OMA.solution : type_of% @OMA.S_mo_302974.main := by
  intro p hp
  refine ⟨DualNumber (ZMod p), inferInstance, ?_⟩
  show ∃ x : WittVector p (DualNumber (ZMod p)),
    x ≠ 0 ∧ (p : WittVector p (DualNumber (ZMod p))) * x = 0
  have hinj : Function.Injective (algebraMap (ZMod p) (DualNumber (ZMod p))) := by
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    exact TrivSqZeroExt.inl_injective
  have hchar : CharP (DualNumber (ZMod p)) p := charP_of_injective_algebraMap hinj p
  refine ⟨WittVector.teichmuller p (DualNumber.eps : DualNumber (ZMod p)), ?_, ?_⟩
  · intro h
    have h0 : (WittVector.teichmuller p (DualNumber.eps : DualNumber (ZMod p))).coeff 0 = 0 := by
      rw [h]
      simp
    rw [WittVector.teichmuller_coeff_zero] at h0
    have h1 := congrArg TrivSqZeroExt.snd h0
    rw [DualNumber.snd_eps, TrivSqZeroExt.snd_zero] at h1
    exact one_ne_zero h1
  · have he : (DualNumber.eps : DualNumber (ZMod p)) ^ p = 0 :=
      pow_eq_zero_of_le hp.out.two_le (by rw [sq, DualNumber.eps_mul_eps])
    have hF : WittVector.frobenius
        (WittVector.teichmuller p (DualNumber.eps : DualNumber (ZMod p))) = 0 := by
      rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, he,
        WittVector.teichmuller_zero]
    rw [mul_comm, ← WittVector.verschiebung_frobenius, hF, map_zero]
