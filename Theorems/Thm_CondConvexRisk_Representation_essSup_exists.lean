import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem essSup_exists {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : ι → Ω → EReal) (hF : ∀ i, AEMeasurable (F i) P) :
    (∃ Z : Ω → EReal, IsEssSup P F Z) ∧
    (∀ Z Z' : Ω → EReal, IsEssSup P F Z → IsEssSup P F Z' → Z =ᵐ[P] Z') ∧
    (Nonempty ι → IsUpwardDirected P F → ∀ Z : Ω → EReal, IsEssSup P F Z →
      ∃ s : ℕ → ι, ∀ᵐ ω ∂P, Monotone (fun n => F (s n) ω) ∧
        Tendsto (fun n => F (s n) ω) atTop (𝓝 (Z ω))) := by sorry

end CondConvexRisk.Representation
