import OMAStatements.S_mse_1696714
import Mathlib

-- Problem: mse-1696714, for finite groups of the same order, does a strictly smaller derived
-- subgroup force a center that is at least as large?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take G1 = D_3 x D_3 x D_3 and G2 = D_108 (dihedral groups of orders 6 and 216), both of
-- order 216. The center of G1 is trivial, and its derived subgroup lies in the kernel of the
-- surjection G1 -> (Z/2)^3 (rotation / reflection in each factor), which has 27 elements.
-- In D_108 the commutator of r and s is r^2, of order 54, so the derived subgroup has at least
-- 54 elements, and r^54 is a nontrivial central element. So |G1'| <= 27 < 54 <= |G2'| but
-- |Z(G2)| >= 2 > 1 = |Z(G1)|.

namespace MSE1696714

abbrev G₁ : Type := DihedralGroup 3 × DihedralGroup 3 × DihedralGroup 3

abbrev G₂ : Type := DihedralGroup 108

def sgn : DihedralGroup 3 →* Multiplicative (ZMod 2) where
  toFun d := match d with
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by decide

theorem sgn_surj : Function.Surjective sgn := by
  decide

def Φ : G₁ →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  sgn.prodMap (sgn.prodMap sgn)

theorem Φ_surj : Function.Surjective Φ := by
  rintro ⟨a, b, c⟩
  obtain ⟨x, rfl⟩ := sgn_surj a
  obtain ⟨y, rfl⟩ := sgn_surj b
  obtain ⟨z, rfl⟩ := sgn_surj c
  exact ⟨(x, y, z), rfl⟩

theorem card_G₁ : Nat.card G₁ = 216 := by
  have h := DihedralGroup.nat_card (n := 3)
  have h2 : Nat.card G₁ = 2 * 3 * (2 * 3 * (2 * 3)) := by
    rw [Nat.card_prod, Nat.card_prod, h]
  exact h2.trans (by norm_num)

theorem card_target : Nat.card
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 8 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem card_ker : Nat.card Φ.ker = 27 := by
  have h1 := Subgroup.card_mul_index Φ.ker
  have h2 : Φ.ker.index = 8 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr Φ_surj, Subgroup.card_top, card_target]
  rw [h2, card_G₁] at h1
  omega

theorem comm_G₂ : 54 ≤ Nat.card (commutator G₂) := by
  have hmem : (DihedralGroup.r 2 : G₂) ∈ commutator G₂ := by
    have h : (DihedralGroup.r 1 : G₂) * (DihedralGroup.sr 0 : G₂) * (DihedralGroup.r 1 : G₂)⁻¹ *
        (DihedralGroup.sr 0 : G₂)⁻¹ = (DihedralGroup.r 2 : G₂) := by
      decide
    have h2 := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top (DihedralGroup.r 1 : G₂)) (Subgroup.mem_top (DihedralGroup.sr 0 : G₂))
    rw [commutatorElement_def, h] at h2
    exact h2
  have hle : Subgroup.zpowers (DihedralGroup.r 2 : G₂) ≤ commutator G₂ :=
    Subgroup.zpowers_le.mpr hmem
  have hcard : Nat.card (Subgroup.zpowers (DihedralGroup.r 2 : G₂)) = 54 := by
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r]
    rfl
  have hle2 := Subgroup.card_le_of_le hle
  rw [hcard] at hle2
  exact hle2

theorem center_G₂ : 1 < Nat.card (Subgroup.center G₂) := by
  rw [Subgroup.one_lt_card_iff_ne_bot]
  intro hbot
  have hmem : (DihedralGroup.r 54 : G₂) ∈ Subgroup.center G₂ := by
    rw [Subgroup.mem_center_iff]
    intro g
    cases g with
    | r i =>
      rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
    | sr i =>
      have h : (54 : ZMod 108) = -54 := by decide
      rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, sub_eq_add_neg, ← h]
  rw [hbot, Subgroup.mem_bot] at hmem
  exact absurd hmem (by decide)

theorem center_G₁ : Nat.card (Subgroup.center G₁) = 1 := by
  have h3 : Subgroup.center (DihedralGroup 3) = ⊥ :=
    DihedralGroup.center_eq_bot_of_odd_ne_one ⟨1, rfl⟩ (by decide)
  rw [Subgroup.center_prod, Subgroup.center_prod, h3, Subgroup.bot_prod_bot,
    Subgroup.bot_prod_bot, Subgroup.card_bot]

end MSE1696714

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_1696714.main) := by
  intro h
  have hcard : Nat.card MSE1696714.G₁ = Nat.card MSE1696714.G₂ := by
    rw [MSE1696714.card_G₁, DihedralGroup.nat_card]
  have hcomm : Nat.card (commutator MSE1696714.G₁) < Nat.card (commutator MSE1696714.G₂) := by
    have h1 := Subgroup.card_le_of_le (Abelianization.commutator_subset_ker MSE1696714.Φ)
    rw [MSE1696714.card_ker] at h1
    have h2 := MSE1696714.comm_G₂
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le (by norm_num) h2)
  have hmain := h MSE1696714.G₁ MSE1696714.G₂ hcard hcomm
  rw [MSE1696714.center_G₁] at hmain
  have h3 := MSE1696714.center_G₂
  exact absurd hmain (not_le.mpr h3)
