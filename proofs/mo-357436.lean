import OMAStatements.S_mo_357436
import Mathlib

-- Problem: mo-357436, |A x|^2 = f'(|x|^2) for all x with f convex and differentiable on
-- [0, infinity) if and only if A^T A = c I for some c >= 0.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- If A^T A = c I with c >= 0, take f(t) = c t^2 / 2: it is convex, f'(t) = c t and
-- |A x|^2 = x . (A^T A x) = c |x|^2. Conversely, if |A x|^2 = phi(|x|^2) for all x, then for
-- x != 0 the unit vector u = x / |x| gives |A x|^2 = |x|^2 |A u|^2 = phi(1) |x|^2, so
-- |A x|^2 = c |x|^2 with c = phi(1) = |A e_0|^2 >= 0. Polarization gives (A x) . (A y) = c x . y,
-- and evaluating at the standard basis vectors gives A^T A = c I. (For n = 0 take c = 0.)

open Matrix Set

namespace MO357436

open OMA.S_mo_357436

theorem key {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ ((Aᵀ * A) *ᵥ y) := by
  calc (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = (x ᵥ* Aᵀ) ⬝ᵥ (A *ᵥ y) := by rw [Matrix.vecMul_transpose]
    _ = x ⬝ᵥ (Aᵀ *ᵥ (A *ᵥ y)) := (Matrix.dotProduct_mulVec x Aᵀ (A *ᵥ y)).symm
    _ = x ⬝ᵥ ((Aᵀ * A) *ᵥ y) := by rw [Matrix.mulVec_mulVec]

theorem sqDot_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ sqDot x := by
  unfold sqDot dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

theorem backward {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hA : Aᵀ * A = c • 1) :
    ∃ f : ℝ → ℝ, ConvexOn ℝ (Ici 0) f ∧ DifferentiableOn ℝ f (Ici 0) ∧
      ∀ x : Fin n → ℝ, sqDot (A *ᵥ x) = derivWithin f (Ici 0) (sqDot x) := by
  have hd : ∀ s : ℝ, HasDerivAt (fun t : ℝ => c / 2 * (t * t)) (c * s) s := by
    intro s
    have h := ((hasDerivAt_id' s).mul (hasDerivAt_id' s)).const_mul (c / 2)
    have h' : HasDerivAt (fun t : ℝ => c / 2 * (t * t)) (c / 2 * (1 * s + s * 1)) s := h
    have e : c / 2 * (1 * s + s * 1) = c * s := by ring
    rw [e] at h'
    exact h'
  refine ⟨fun t => c / 2 * (t * t), ?_, ?_, ?_⟩
  · have h := (convexOn_pow 2 : ConvexOn ℝ (Ici 0) fun x : ℝ => x ^ 2).smul
      (show (0 : ℝ) ≤ c / 2 by positivity)
    have e : (fun t : ℝ => c / 2 * (t * t)) = fun t => (c / 2) • t ^ 2 := by
      funext t
      rw [smul_eq_mul]
      ring
    rw [e]
    exact h
  · intro s _
    exact (hd s).differentiableAt.differentiableWithinAt
  · intro x
    have hs : sqDot x ∈ Ici (0 : ℝ) := sqDot_nonneg x
    rw [(hd (sqDot x)).differentiableAt.derivWithin (uniqueDiffOn_Ici 0 _ hs),
      (hd (sqDot x)).deriv]
    unfold sqDot
    rw [key A x x, hA, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

theorem forward {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (φ : ℝ → ℝ)
    (hid : ∀ x : Fin n → ℝ, sqDot (A *ᵥ x) = φ (sqDot x)) :
    ∃ c : ℝ, 0 ≤ c ∧ Aᵀ * A = c • 1 := by
  cases n with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    ext i j
    exact i.elim0
  | succ k =>
    have he : sqDot (Pi.single (0 : Fin (k + 1)) (1 : ℝ)) = 1 := by
      unfold sqDot
      rw [single_one_dotProduct, Pi.single_eq_same]
    have hc0 : 0 ≤ φ 1 := by
      have h := hid (Pi.single 0 1)
      rw [he] at h
      rw [← h]
      exact sqDot_nonneg _
    have scale : ∀ (t : ℝ) (x : Fin (k + 1) → ℝ), sqDot (t • x) = t ^ 2 * sqDot x := by
      intro t x
      unfold sqDot
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    have Q : ∀ x : Fin (k + 1) → ℝ, sqDot (A *ᵥ x) = φ 1 * sqDot x := by
      intro x
      rcases (sqDot_nonneg x).lt_or_eq with hpos | h0
      · have hu : sqDot ((Real.sqrt (sqDot x))⁻¹ • x) = 1 := by
          rw [scale, inv_pow, Real.sq_sqrt hpos.le]
          exact inv_mul_cancel₀ hpos.ne'
        have h1 := hid ((Real.sqrt (sqDot x))⁻¹ • x)
        rw [hu, Matrix.mulVec_smul, scale, inv_pow, Real.sq_sqrt hpos.le] at h1
        have h2 : sqDot (A *ᵥ x) = sqDot x * ((sqDot x)⁻¹ * sqDot (A *ᵥ x)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
        rw [h2, h1]
        ring
      · have hx : x = 0 := dotProduct_self_eq_zero.mp h0.symm
        subst hx
        simp [sqDot]
    have pol : ∀ x y : Fin (k + 1) → ℝ, (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = φ 1 * (x ⬝ᵥ y) := by
      intro x y
      have hxy := Q (x + y)
      have hx := Q x
      have hy := Q y
      unfold sqDot at hxy hx hy
      have c1 := dotProduct_comm (A *ᵥ y) (A *ᵥ x)
      have c2 := dotProduct_comm y x
      simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add] at hxy
      rw [c1, c2] at hxy
      linarith
    refine ⟨φ 1, hc0, ?_⟩
    ext i j
    have h1 := pol (Pi.single i 1) (Pi.single j 1)
    rw [key A, single_one_dotProduct, single_one_dotProduct, Matrix.mulVec_single_one,
      Pi.single_apply] at h1
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    exact h1

end MO357436

theorem OMA.solution : type_of% @OMA.S_mo_357436.main := by
  intro n A
  constructor
  · rintro ⟨f, _, _, hid⟩
    exact MO357436.forward A (derivWithin f (Set.Ici 0)) hid
  · rintro ⟨c, hc, hA⟩
    exact MO357436.backward A c hc hA
