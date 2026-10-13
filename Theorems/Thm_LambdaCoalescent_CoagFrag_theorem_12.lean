import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting

namespace LambdaCoalescent.CoagFrag

open MeasureTheory

theorem theorem_12 (α β θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : -(α * β) < θ)
    (μ ν ρ κ : Measure LambdaCoalescent.Rates.PInf) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure κ]
    (hμ : IsEPFLaw (pdEPF α θ) μ) (hν : IsEPFLaw (pdEPF β (θ / α)) ν)
    (hρ : IsEPFLaw (pdEPF (α * β) θ) ρ) (hκ : IsEPFLaw (pdEPF α (-(α * β))) κ) :
    ∀ S : Set (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf), MeasurableSet S →
      (μ.prod ν) {x | (x.1, coag x.1 x.2) ∈ S} =
        (ρ.prod (Measure.infinitePi (fun _ : ℕ => κ))) {y | (frag y.1 y.2, y.1) ∈ S} := by sorry

end LambdaCoalescent.CoagFrag

