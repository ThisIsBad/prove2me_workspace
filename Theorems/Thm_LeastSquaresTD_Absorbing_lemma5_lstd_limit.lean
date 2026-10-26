import Definitions.Def_LeastSquaresTD_Absorbing_Estimator

namespace LeastSquaresTD.Absorbing

open MeasureTheory Filter Topology

variable {m : ℕ}

/-- Lemma 5, p. 43, for any finite Markov chain. The paper's `θ_LSTD` is
the limit of the estimates; `Tendsto` asserts that this limit exists.
Equation (11) uses every transition of this ordinary chain. -/
theorem lemma5_lstd_limit
    {X Ω : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Chain X) (S : X → ℝ) (R : X → X → ℝ)
    (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ) (Z : ℕ → Ω → X)
    (hS_nonneg : ∀ x, 0 ≤ S x) (hS_sum : ∑ x, S x = 1)
    (hlaw : HasChainLaw C S μ Z)
    (hvisits : ∀ᵐ ω ∂μ, ∀ (x : X) (N : ℕ), ∃ n ≥ N, Z n ω = x)
    (hfreq : ∀ᵐ ω ∂μ, ∀ x,
      Tendsto (fun n => chainOutFrequency (fun k => Z k ω) x n) atTop (𝓝 (π x)))
    (hunit : IsUnit (limitMatrix C φ γ π)) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => chainLstdTheta R φ γ (fun k => Z k ω) n)
      atTop (𝓝 (Matrix.mulVec (limitMatrix C φ γ π)⁻¹
        (limitVector C R φ π))) := by sorry

end LeastSquaresTD.Absorbing

