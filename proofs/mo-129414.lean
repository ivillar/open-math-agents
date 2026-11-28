import OMAStatements.S_mo_129414
import Mathlib

-- Problem: mo-129414, a group extension with trivial outer action, noncentral kernel and no
-- homomorphic section.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Take E = S_3 x Z/4 -> G = Z/2, (s, c) -> c mod 2, with kernel N = S_3 x 2Z/4. Conjugation
-- by (s, c) on N agrees with conjugation by (s, 0), which lies in N. The kernel is not
-- central because S_3 is not abelian. A section would give an element (s, c) with c odd and
-- (s, c)^2 = 1, but then 2c = 0 in Z/4 forces c even.

namespace MO129414

def p : Equiv.Perm (Fin 3) × Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) where
  toFun e := Multiplicative.ofAdd (((Multiplicative.toAdd e.2).val : ℕ) : ZMod 2)
  map_one' := by decide
  map_mul' := by
    rintro ⟨σ, x⟩ ⟨τ, y⟩
    show Multiplicative.ofAdd (((Multiplicative.toAdd (x * y)).val : ℕ) : ZMod 2) =
      Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ℕ) : ZMod 2) *
        Multiplicative.ofAdd (((Multiplicative.toAdd y).val : ℕ) : ZMod 2)
    revert x y
    decide

theorem p_apply (e : Equiv.Perm (Fin 3) × Multiplicative (ZMod 4)) :
    p e = Multiplicative.ofAdd (((Multiplicative.toAdd e.2).val : ℕ) : ZMod 2) := rfl

theorem key : ∀ y : Multiplicative (ZMod 4), y * y = 1 →
    Multiplicative.ofAdd (((Multiplicative.toAdd y).val : ℕ) : ZMod 2) ≠
      Multiplicative.ofAdd (1 : ZMod 2) := by
  decide

theorem surj : ∀ g : Multiplicative (ZMod 2), ∃ y : Multiplicative (ZMod 4),
    Multiplicative.ofAdd (((Multiplicative.toAdd y).val : ℕ) : ZMod 2) = g := by
  decide

end MO129414

open OMA.S_mo_129414 in
theorem OMA.solution : type_of% @OMA.S_mo_129414.main := by
  refine ⟨Equiv.Perm (Fin 3) × Multiplicative (ZMod 4), Multiplicative (ZMod 2), inferInstance,
    inferInstance, MO129414.p, ?_, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨y, hy⟩ := MO129414.surj g
    exact ⟨(1, y), hy⟩
  · intro e
    refine ⟨(e.1, 1), ?_, ?_⟩
    · rw [MonoidHom.mem_ker, MO129414.p_apply]
      show Multiplicative.ofAdd
        (((Multiplicative.toAdd (1 : Multiplicative (ZMod 4))).val : ℕ) : ZMod 2) = 1
      decide
    · intro n _
      refine Prod.ext rfl ?_
      show e.2 * n.2 * e.2⁻¹ = 1 * n.2 * 1⁻¹
      rw [mul_comm e.2 n.2, mul_inv_cancel_right, one_mul, inv_one, mul_one]
  · intro hc
    have hmem : ((Equiv.swap 0 1, 1) : Equiv.Perm (Fin 3) × Multiplicative (ZMod 4)) ∈
        MO129414.p.ker := by
      rw [MonoidHom.mem_ker, MO129414.p_apply]
      decide
    have h1 := congrArg Prod.fst (hc _ hmem (Equiv.swap 1 2, 1))
    revert h1
    decide
  · rintro ⟨s, hs⟩
    have hgg : (Multiplicative.ofAdd (1 : ZMod 2)) * (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
      decide
    have h1 : s (Multiplicative.ofAdd (1 : ZMod 2)) * s (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
      rw [← map_mul, hgg, map_one]
    have h2 : (s (Multiplicative.ofAdd (1 : ZMod 2))).2 * (s (Multiplicative.ofAdd (1 : ZMod 2))).2 = 1 :=
      congrArg Prod.snd h1
    have h3 := hs (Multiplicative.ofAdd (1 : ZMod 2))
    rw [MO129414.p_apply] at h3
    exact MO129414.key _ h2 h3
