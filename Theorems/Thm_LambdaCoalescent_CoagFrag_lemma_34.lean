import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting

namespace LambdaCoalescent.CoagFrag

open MeasureTheory

theorem lemma_34 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ : Ω → LambdaCoalescent.Rates.PInf) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (p₁ p : Multiset ℕ → ℝ) (μ₁ ν : Measure LambdaCoalescent.Rates.PInf) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν]
    (hμ₁ : IsEPFLaw p₁ μ₁) (hν : IsEPFLaw p ν) :
    (P.map X₁ = μ₁ ∧
        ∀ S : Set (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf), MeasurableSet S →
          P {ω | (X₁ ω, X₂ ω) ∈ S} = (μ₁.prod ν) {x | (x.1, coag x.1 x.2) ∈ S}) ↔
      ∀ (n : ℕ) (π₁ π₂ : Setoid (Fin n)), π₁ ≤ π₂ →
        P.real {ω | restrict n (X₁ ω) = π₁ ∧ restrict n (X₂ ω) = π₂} =
          p₁ (blockSizes π₁) * p (coagCounts π₁ π₂) := by sorry

end LambdaCoalescent.CoagFrag

