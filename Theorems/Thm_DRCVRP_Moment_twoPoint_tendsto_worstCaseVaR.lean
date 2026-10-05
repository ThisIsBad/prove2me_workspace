import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Moment_AmbiguitySet

open MeasureTheory Filter Topology

namespace DRCVRP.Moment

theorem twoPoint_tendsto_worstCaseVaR {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (σ : Fin p → ℝ) (ε : ℝ)
    (hqlo : ∀ i, 0 ≤ qlo i)
    (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (hφ : ∀ l, ConvexOn ℝ Set.univ (φ l))
    (hσ : ∀ l, φ l μ < σ l)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (S : Finset (Fin n)) :
    ∃ (p₁ p₂ : ℕ → ℝ) (q₁ q₂ : ℕ → Fin n → ℝ),
      (∀ t, 0 ≤ p₁ t ∧ 0 ≤ p₂ t ∧ q₁ t ∈ Set.Icc qlo qhi ∧ q₂ t ∈ Set.Icc qlo qhi ∧
        twoPointMeasure (p₁ t) (p₂ t) (q₁ t) (q₂ t) ∈ momentAmbiguitySet qlo qhi μ φ σ) ∧
      Tendsto
        (fun t => MultistageStochastic.valueAtRisk (twoPointMeasure (p₁ t) (p₂ t) (q₁ t) (q₂ t))
          (fun q => ∑ i ∈ S, q i) (1 - ε))
        atTop (𝓝 (worstCaseVaR (momentAmbiguitySet qlo qhi μ φ σ) ε S)) := by sorry

end DRCVRP.Moment

