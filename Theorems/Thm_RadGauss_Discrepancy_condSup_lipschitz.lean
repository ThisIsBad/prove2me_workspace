import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_Discrepancy_maxDiscrepancy
import Definitions.Def_RadGauss_Discrepancy_condSup

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Discrepancy

/-- Appendix A, p. 479: the Lipschitz condition `|s(n₁) − s(n₂)| ≤ 4|n₂ − n₁|/n`, stated for
every pair of values attained by `Σ_i σ_i` (the page writes `0 ≤ n₂ < n₁ ≤ n`). -/
theorem condSup_lipschitz {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (hFne : F.Nonempty)
    (hFrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hsup : ∀ σ : Fin n → Bool,
      Measurable fun x : Fin n → X => ⨆ f : F, ∑ i, RadGauss.RiskBound.signVal (σ i) * (f : X → ℝ) (x i))
    (N₁ N₂ : ℤ) (hN₁ : ∃ σ : Fin n → Bool, sumSign σ = N₁)
    (hN₂ : ∃ σ : Fin n → Bool, sumSign σ = N₂) :
    |condSup μ n F N₁ - condSup μ n F N₂| ≤ 4 * |(N₂ : ℝ) - N₁| / n := by sorry

end RadGauss.Discrepancy

