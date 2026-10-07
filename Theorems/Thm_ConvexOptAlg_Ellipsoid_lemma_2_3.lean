import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs

namespace ConvexOptAlg.Ellipsoid

open Matrix MeasureTheory

/-- **Lemma 2.3** (Bubeck, arXiv:1405.4980v2, p. 247). Let `E₀ = {x : (x − c₀)⊤H₀⁻¹(x − c₀) ≤ 1}`
with `H₀` symmetric positive definite, and let `w ≠ 0`.
(i) There is an ellipsoid `E` (center `c`, symmetric positive definite matrix `H`) containing
the half-ellipsoid `{x ∈ E₀ : w⊤(x − c₀) ≤ 0}` (2.3) with `vol(E) ≤ exp(−1/(2n)) vol(E₀)` (2.4).
(ii) For `n ≥ 2` one can take `c = c₀ − (1/(n+1)) H₀w/√(w⊤H₀w)` (2.5) and
`H = (n²/(n²−1)) (H₀ − (2/(n+1)) H₀ww⊤H₀/(w⊤H₀w))` (2.6): this `H` is positive definite and
`E` satisfies (2.3) and (2.4). Volume is Lebesgue measure on `ℝⁿ = Fin n → ℝ`. -/
theorem lemma_2_3 {n : ℕ} (c0 : Fin n → ℝ) (H0 : Matrix (Fin n) (Fin n) ℝ) (hH0 : H0.PosDef)
    (w : Fin n → ℝ) (hw : w ≠ 0) :
    (∃ (c : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.PosDef ∧
      LinearOptimization.ellipsoid c0 H0 ∩ {x | w ⬝ᵥ (x - c0) ≤ 0} ⊆
        LinearOptimization.ellipsoid c H ∧
      volume (LinearOptimization.ellipsoid c H) ≤
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * (n : ℝ)))) *
          volume (LinearOptimization.ellipsoid c0 H0)) ∧
    (2 ≤ n →
      (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
          (H0 - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H0 *ᵥ w))⁻¹ •
            (H0 * vecMulVec w w * H0))).PosDef ∧
      LinearOptimization.ellipsoid c0 H0 ∩ {x | w ⬝ᵥ (x - c0) ≤ 0} ⊆
        LinearOptimization.ellipsoid
          (c0 - ((1 : ℝ) / ((n : ℝ) + 1)) • (Real.sqrt (w ⬝ᵥ (H0 *ᵥ w)))⁻¹ • (H0 *ᵥ w))
          (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
            (H0 - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H0 *ᵥ w))⁻¹ •
              (H0 * vecMulVec w w * H0))) ∧
      volume (LinearOptimization.ellipsoid
          (c0 - ((1 : ℝ) / ((n : ℝ) + 1)) • (Real.sqrt (w ⬝ᵥ (H0 *ᵥ w)))⁻¹ • (H0 *ᵥ w))
          (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
            (H0 - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H0 *ᵥ w))⁻¹ •
              (H0 * vecMulVec w w * H0)))) ≤
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * (n : ℝ)))) *
          volume (LinearOptimization.ellipsoid c0 H0)) := by sorry

end ConvexOptAlg.Ellipsoid

