import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting

namespace LambdaCoalescent.CoagFrag

open MeasureTheory

theorem lemma_35 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ : Ω → LambdaCoalescent.Rates.PInf) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (p₂ phat : Multiset ℕ → ℝ) (μ₂ νhat : Measure LambdaCoalescent.Rates.PInf)
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure νhat]
    (hμ₂ : IsEPFLaw p₂ μ₂) (hνhat : IsEPFLaw phat νhat) :
    (P.map X₂ = μ₂ ∧
        ∀ S : Set (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf), MeasurableSet S →
          P {ω | (X₁ ω, X₂ ω) ∈ S} =
            (μ₂.prod (Measure.infinitePi (fun _ : ℕ => νhat))) {y | (frag y.1 y.2, y.1) ∈ S}) ↔
      ∀ (n : ℕ) (π₁ π₂ : Setoid (Fin n)), π₁ ≤ π₂ →
        P.real {ω | restrict n (X₁ ω) = π₁ ∧ restrict n (X₂ ω) = π₂} =
          ((fragSizes π₁ π₂).map phat).prod * p₂ (blockSizes π₂) := by sorry

end LambdaCoalescent.CoagFrag

