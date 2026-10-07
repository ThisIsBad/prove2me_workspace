import Mathlib
import Definitions.Def_ConvexOptAlg_StochMD_Defs

namespace ConvexOptAlg.StochMD

open MeasureTheory

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 6.3, printed p. 333, fourth display ("In
particular this yields …"): in the setting of Theorem 6.3, for a run of S-MD with step size
`1/(β + 1/η)` (any `η > 0`) driven by a stochastic oracle that is conditionally unbiased for `∇f`
with conditional variance at most `σ²`, for every `s ≥ 1` and every `x∗ ∈ X`, the random variables
`f(x_{s+1})` and `D_Φ(x∗, x_s) − D_Φ(x∗, x_{s+1})` are integrable and
`E f(x_{s+1}) − f(x∗) ≤ (β + 1/η) E(D_Φ(x∗, x_s) − D_Φ(x∗, x_{s+1})) + ησ²/2`. -/
theorem thm_6_3_expected_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X D : Set E) (hXcpt : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (hΦsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' 1)
    (x₁ : E) (R : ℝ) (hR : ∀ z ∈ X ∩ D, Φ z - Φ x₁ ≤ R ^ 2)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsSmoothWRT X f f' β)
    (σ : ℝ) (x : ℕ → Ω → E) (gt : ℕ → Ω → E →L[ℝ] ℝ)
    (horacle : IsSmoothStochOracle μ f' σ x gt)
    (η : ℝ) (hη : 0 < η) (hrun : IsSMDRun X D Φ Φ' (1 / (β + 1 / η)) x₁ x gt)
    (xstar : E) (hxstar : xstar ∈ X) (s : ℕ) (hs : 1 ≤ s) :
    Integrable (fun ω => f (x (s + 1) ω)) μ ∧
      Integrable (fun ω => bregman Φ Φ' xstar (x s ω) - bregman Φ Φ' xstar (x (s + 1) ω)) μ ∧
      (∫ ω, f (x (s + 1) ω) ∂μ) - f xstar ≤
        (β + 1 / η) *
            (∫ ω, (bregman Φ Φ' xstar (x s ω) - bregman Φ Φ' xstar (x (s + 1) ω)) ∂μ) +
          η * σ ^ 2 / 2 := by sorry

end ConvexOptAlg.StochMD

