import Mathlib

namespace LogRegretOCO.FTAL

/-- Scalar inequality: `1 - α z ≤ exp (-(α (z + β/2 z²)))` when `0 < β`, `2β ≤ α`, `β|z| ≤ 1/8`. -/
theorem aux_ecalb_scalar (α β z : ℝ) (hα : 0 < α) (hβ : 0 < β) (hβα : 2 * β ≤ α)
    (hz : β * |z| ≤ 1 / 8) : 1 - α * z ≤ Real.exp (-(α * (z + β / 2 * z ^ 2))) := by
  rcases le_or_gt 0 z with hz0 | hz0
  · rcases le_or_gt 1 (α * z) with hu | hu
    · have := Real.exp_pos (-(α * (z + β / 2 * z ^ 2)))
      linarith
    · have hu0 : 0 ≤ α * z := mul_nonneg hα.le hz0
      have habs : |α * z| < 1 := by rw [abs_of_nonneg hu0]; exact hu
      have hs := Real.hasSum_pow_div_log_of_abs_lt_one habs
      have hle := sum_le_hasSum (Finset.range 2)
        (fun i _ => div_nonneg (pow_nonneg hu0 _) (by positivity)) hs
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
      norm_num at hle
      have h1 : 0 < 1 - α * z := by linarith
      have hprod : 0 ≤ α * z ^ 2 * (α - β) :=
        mul_nonneg (mul_nonneg hα.le (sq_nonneg z)) (by linarith)
      have key : α * (z + β / 2 * z ^ 2) ≤ -Real.log (1 - α * z) := by nlinarith
      calc 1 - α * z = Real.exp (Real.log (1 - α * z)) := (Real.exp_log h1).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · have hw : 0 < -z := neg_pos.mpr hz0
    rw [abs_of_neg hz0] at hz
    have hq : 15 / 16 ≤ 1 - β * (-z) / 2 := by linarith
    have hs_eq : -(α * (z + β / 2 * z ^ 2)) = α * (-z) * (1 - β * (-z) / 2) := by ring
    have hs0 : 0 ≤ α * (-z) * (1 - β * (-z) / 2) :=
      mul_nonneg (mul_nonneg hα.le hw.le) (by linarith)
    have h1 : (1 / 2 : ℝ) ≤ (1 - β * (-z) / 2) ^ 2 := by nlinarith
    have h2 : α * β * z ^ 2 ≤ α ^ 2 * z ^ 2 * (1 / 2) := by
      nlinarith [mul_nonneg hα.le (sq_nonneg z)]
    have h3 : α ^ 2 * z ^ 2 * (1 / 2) ≤ α ^ 2 * z ^ 2 * (1 - β * (-z) / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have hq2 := Real.quadratic_le_exp_of_nonneg hs0
    rw [hs_eq]
    have h4 : (α * (-z) * (1 - β * (-z) / 2)) ^ 2 = α ^ 2 * z ^ 2 * (1 - β * (-z) / 2) ^ 2 := by
      ring
    have h5 : α * (-z) * (1 - β * (-z) / 2) = -(α * z) - α * β * z ^ 2 / 2 := by ring
    linarith

/-- Tangent-line inequality for a concave function differentiable at a point of its domain. -/
theorem aux_ecalb_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Set E)
    (h : E → ℝ) (hc : ConcaveOn ℝ P h) {x y : E} (hx : x ∈ P) (hy : y ∈ P)
    (hd : DifferentiableAt ℝ h y) : h x ≤ h y + fderiv ℝ h y (x - y) := by
  have h1 : HasDerivAt (fun t : ℝ => y + t • (x - y)) (x - y) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (x - y)).const_add y
  have h2 : HasFDerivAt h (fderiv ℝ h y) (y + (0 : ℝ) • (x - y)) := by
    simpa using hd.hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ => h (y + t • (x - y))) (fderiv ℝ h y (x - y)) 0 :=
    h2.comp_hasDerivAt (0 : ℝ) h1
  have ht := hg.tendsto_slope_zero_right
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      h x - h y ≤ t⁻¹ • ((fun t : ℝ => h (y + t • (x - y))) (0 + t)
        - (fun t : ℝ => h (y + t • (x - y))) 0) := by
    filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with t ht
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    have key := hc.2 hy hx (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
    have heq : (1 - t) • y + t • x = y + t • (x - y) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq, smul_eq_mul, smul_eq_mul] at key
    rw [le_inv_mul_iff₀ ht.1]
    nlinarith
  have := ge_of_tendsto ht hev
  linarith

end LogRegretOCO.FTAL

open LogRegretOCO.FTAL

theorem solution {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (D G α β : ℝ)
    (hPconv : Convex ℝ P) (hD : 0 < D) (hG : 0 < G) (hα : 0 < α)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (hdiff : ∀ x ∈ P, DifferentiableAt ℝ f x)
    (hgrad : ∀ x ∈ P, ‖gradient f x‖ ≤ G)
    (hexp : ConcaveOn ℝ P (fun x => Real.exp (-α * f x)))
    (hβ0 : 0 < β) (hβ : β ≤ 1 / 2 * min (1 / (4 * G * D)) α) :
    ∀ x ∈ P, ∀ y ∈ P,
      f y + inner ℝ (gradient f y) (x - y) + β / 2 * (inner ℝ (gradient f y) (x - y)) ^ 2
        ≤ f x := by
  intro x hx y hy
  have h4 : 0 < 4 * G * D := by positivity
  have hβα : 2 * β ≤ α := by
    have := min_le_right (1 / (4 * G * D)) α
    linarith
  have hβGD : β * (4 * G * D) ≤ 1 / 2 := by
    have hb : β ≤ 1 / 2 * (1 / (4 * G * D)) := by
      have := min_le_left (1 / (4 * G * D)) α
      linarith
    have := mul_le_mul_of_nonneg_right hb h4.le
    rwa [show 1 / 2 * (1 / (4 * G * D)) * (4 * G * D) = 1 / 2 by field_simp] at this
  set z := inner ℝ (gradient f y) (x - y) with hz_def
  have hzabs : |z| ≤ G * D := by
    have h1 := abs_real_inner_le_norm (gradient f y) (x - y)
    have h2 := mul_le_mul (hgrad y hy) (hdiam x hx y hy) (norm_nonneg _) hG.le
    linarith
  have hbz : β * |z| ≤ 1 / 8 := by
    have := mul_le_mul_of_nonneg_left hzabs hβ0.le
    nlinarith
  -- derivative of exp(-α f) at y
  have hdy := (hdiff y hy).hasFDerivAt
  have hH : HasFDerivAt (fun x => Real.exp (-α * f x))
      (Real.exp (-α * f y) • ((-α) • fderiv ℝ f y)) y := (hdy.const_mul (-α)).exp
  have htan := aux_ecalb_tangent P (fun x => Real.exp (-α * f x)) hexp hx hy
    hH.differentiableAt
  rw [hH.fderiv] at htan
  have hfz : fderiv ℝ f y (x - y) = z := by
    rw [hz_def, gradient, InnerProductSpace.toDual_symm_apply]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hfz] at htan
  have hsc := aux_ecalb_scalar α β z hα hβ0 hβα hbz
  have hey := Real.exp_pos (-α * f y)
  have hchain : Real.exp (-α * f x) ≤ Real.exp (-α * f y + -(α * (z + β / 2 * z ^ 2))) := by
    rw [Real.exp_add]
    have := mul_le_mul_of_nonneg_left hsc hey.le
    nlinarith
  have hlin := Real.exp_le_exp.mp hchain
  have hfin : α * (f y + z + β / 2 * z ^ 2) ≤ α * f x := by linarith
  exact le_of_mul_le_mul_left hfin hα
