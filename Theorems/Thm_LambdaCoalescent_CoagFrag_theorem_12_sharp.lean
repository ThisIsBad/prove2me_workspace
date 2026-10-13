import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting

namespace LambdaCoalescent.CoagFrag

open MeasureTheory

theorem theorem_12_sharp (α θ αc θc α₁ θ₁ αf θf : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (hαc0 : 0 ≤ αc) (hαc1 : αc < 1) (hθc : -αc < θc)
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1) (hθ₁ : -α₁ < θ₁)
    (hαf0 : 0 ≤ αf) (hαf1 : αf < 1) (hθf : -αf < θf) :
    (∀ (μ ν ρ κ : Measure LambdaCoalescent.Rates.PInf) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
        [IsProbabilityMeasure ρ] [IsProbabilityMeasure κ],
        IsEPFLaw (pdEPF α θ) μ → IsEPFLaw (pdEPF αc θc) ν →
        IsEPFLaw (pdEPF α₁ θ₁) ρ → IsEPFLaw (pdEPF αf θf) κ →
        ∀ S : Set (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf), MeasurableSet S →
          (μ.prod ν) {x | (x.1, coag x.1 x.2) ∈ S} =
            (ρ.prod (Measure.infinitePi (fun _ : ℕ => κ))) {y | (frag y.1 y.2, y.1) ∈ S}) ↔
      (αf = α ∧ θf = -α₁ ∧ α₁ = α * αc ∧ α * θc = θ ∧ θ₁ = θ) := by sorry

end LambdaCoalescent.CoagFrag

