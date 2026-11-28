import OMAStatements.S_mo_98927
import Mathlib

-- Problem: mo-98927, if the normal closures of x and y meet trivially, is the product of the
-- indices of the cyclic groups of x and y in their normal closures equal to the index of the
-- cyclic group of x y in its normal closure?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Let G = D_3 x D_3, x = (r, 1), y = (1, r) with r a rotation of order 3. The cyclic groups
-- of x and y are normal and meet trivially, so both indices on the left are 1. But conjugating
-- x y = (r, r) by (s, 1) gives (r^2, r), which is not a power of (r, r), so the normal closure
-- of x y is strictly bigger than its cyclic group and the index on the right is not 1.

open Subgroup

namespace MO98927

abbrev G : Type := DihedralGroup 3 × DihedralGroup 3

def x : G := (DihedralGroup.r 1, 1)

def y : G := (1, DihedralGroup.r 1)

theorem conj_r : ∀ d : DihedralGroup 3,
    d * DihedralGroup.r 1 * d⁻¹ = DihedralGroup.r 1 ∨
      d * DihedralGroup.r 1 * d⁻¹ = (DihedralGroup.r 1)⁻¹ := by
  decide

theorem conj_x (g : G) : g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹ := by
  rcases conj_r g.1 with h | h
  · left
    exact Prod.ext h (by simp [x])
  · right
    exact Prod.ext h (by simp [x])

theorem conj_y (g : G) : g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y⁻¹ := by
  rcases conj_r g.2 with h | h
  · left
    exact Prod.ext (by simp [y]) h
  · right
    exact Prod.ext (by simp [y]) h

theorem normal_of_conj (u : G) (hu : ∀ g : G, g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u⁻¹) :
    (zpowers u).Normal := by
  constructor
  intro n hn g
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  rw [← conj_zpow]
  apply Subgroup.zpow_mem
  rcases hu g with h | h
  · rw [h]
    exact Subgroup.mem_zpowers u
  · rw [h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers u)

instance normal_x : (zpowers x).Normal := normal_of_conj x conj_x

instance normal_y : (zpowers y).Normal := normal_of_conj y conj_y

theorem le_x : normalClosure {x} ≤ zpowers x :=
  normalClosure_le_normal (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers x))

theorem le_y : normalClosure {y} ≤ zpowers y :=
  normalClosure_le_normal (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers y))

theorem hyp : normalClosure {x} ⊓ normalClosure {y} = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (le_x hg.1)
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (le_y hg.2)
  rw [Subgroup.mem_bot]
  have e1 : g.2 = 1 := by
    rw [← hk]
    simp [x]
  have e2 : g.1 = 1 := by
    rw [← hl]
    simp [y]
  exact Prod.ext e2 e1

theorem cube : (x * y) ^ 3 = 1 := by
  decide

theorem not_pow : ∀ m : Fin 3,
    (x * y) ^ (m : ℕ) ≠ ((DihedralGroup.sr 0, 1) : G) * (x * y) * ((DihedralGroup.sr 0, 1) : G)⁻¹ := by
  decide

end MO98927

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_98927.main) := by
  intro h
  have hmain := h MO98927.G MO98927.x MO98927.y MO98927.hyp
  have i1 : (zpowers MO98927.x).relIndex (normalClosure {MO98927.x}) = 1 :=
    Subgroup.relIndex_eq_one.mpr MO98927.le_x
  have i2 : (zpowers MO98927.y).relIndex (normalClosure {MO98927.y}) = 1 :=
    Subgroup.relIndex_eq_one.mpr MO98927.le_y
  rw [i1, i2, one_mul] at hmain
  have hle := Subgroup.relIndex_eq_one.mp hmain.symm
  have hz : ((DihedralGroup.sr 0, 1) : MO98927.G) * (MO98927.x * MO98927.y) *
      ((DihedralGroup.sr 0, 1) : MO98927.G)⁻¹ ∈ normalClosure {MO98927.x * MO98927.y} :=
    Subgroup.normalClosure_normal.conj_mem _
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) _
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hle hz))
  have hred : (MO98927.x * MO98927.y) ^ n = (MO98927.x * MO98927.y) ^ (n % 3) := by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, MO98927.cube, one_pow, one_mul]
  rw [hred] at hn
  exact MO98927.not_pow ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩ hn
