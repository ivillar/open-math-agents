import OMAStatements.S_mo_453534
import Mathlib

-- Problem: mo-453534, in a Euclidean domain can the remainder r of a = bq + r always be chosen
-- with a - r = 0 or deg (a - r) <= deg a?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. On the integers take deg n = floor (log_2 |n|). Balanced remainders (|r| <= |b| / 2) show
-- that this is a Euclidean degree function, and deg a <= deg (a b) holds because |a| <= |a b|.
-- For a = 30 and b = 11 a remainder r with r = 0 or deg r < deg 11 = 3 must satisfy |r| < 8 and
-- r = 30 mod 11, so r = -3; then a - r = 33 has degree 5 > 4 = deg 30.

namespace MO453534

def deg (n : ℤ) : ℕ := Nat.log 2 n.natAbs

theorem deg_lt (r b : ℤ) (hr : r ≠ 0) (h : 2 * r.natAbs ≤ b.natAbs) : deg r < deg b := by
  unfold deg
  have h1 : Nat.log 2 (r.natAbs * 2) = Nat.log 2 r.natAbs + 1 :=
    Nat.log_mul_base (by norm_num) (Int.natAbs_ne_zero.mpr hr)
  have h2 : Nat.log 2 (r.natAbs * 2) ≤ Nat.log 2 b.natAbs :=
    Nat.log_mono_right (by omega)
  omega

theorem core (a b s t : ℤ) (hb : b ≠ 0) (h0 : 0 ≤ s) (h1 : s < (b.natAbs : ℤ))
    (h : b * t + s = a) : ∃ q r : ℤ, a = b * q + r ∧ (r = 0 ∨ deg r < deg b) := by
  by_cases hc : 2 * s ≤ (b.natAbs : ℤ)
  · refine ⟨t, s, h.symm, ?_⟩
    by_cases hz : s = 0
    · left
      exact hz
    · right
      exact deg_lt _ _ hz (by omega)
  · rcases lt_or_gt_of_ne hb with hneg | hpos
    · exact ⟨t - 1, s + b, by linear_combination -h,
        Or.inr (deg_lt _ _ (by omega) (by omega))⟩
    · exact ⟨t + 1, s - b, by linear_combination -h,
        Or.inr (deg_lt _ _ (by omega) (by omega))⟩

theorem euclid : OMA.S_mo_453534.IsEuclideanDegree deg := by
  constructor
  · intro a b hb
    have h0 : 0 ≤ a % b := Int.emod_nonneg a hb
    have h1 : a % b < (b.natAbs : ℤ) := by
      rcases lt_or_gt_of_ne hb with hneg | hpos
      · have h3 := Int.emod_lt_of_pos a (neg_pos.mpr hneg)
        rw [Int.emod_neg] at h3
        exact lt_of_lt_of_le h3 (by omega)
      · have h3 := Int.emod_lt_of_pos a hpos
        exact lt_of_lt_of_le h3 (by omega)
    have h2 : b * (a / b) + a % b = a := by
      rw [Int.emod_def]
      ring
    exact core a b (a % b) (a / b) hb h0 h1 h2
  · intro a b _ hb
    unfold deg
    apply Nat.log_mono_right
    rw [Int.natAbs_mul]
    exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hb)

theorem deg11 : deg 11 = 3 := by
  show Nat.log 2 11 = 3
  exact Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)

theorem deg30 : deg 30 = 4 := by
  show Nat.log 2 30 = 4
  exact Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)

end MO453534

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_453534.main) := by
  intro h
  obtain ⟨q, r, hqr, hr, har⟩ := h ℤ MO453534.deg MO453534.euclid 30 11 (by norm_num)
  rcases hr with hr0 | hrlt
  · omega
  · rw [MO453534.deg11] at hrlt
    have hr8 : r.natAbs < 2 ^ 3 := Nat.lt_pow_of_log_lt (by norm_num) hrlt
    rcases har with h0 | hle
    · omega
    · rw [MO453534.deg30] at hle
      have h5 : Nat.log 2 (30 - r).natAbs < 5 := Nat.lt_succ_of_le hle
      have h32 : (30 - r).natAbs < 2 ^ 5 := Nat.lt_pow_of_log_lt (by norm_num) h5
      omega
