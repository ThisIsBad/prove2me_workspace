import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable
import Definitions.Def_CondConvexRisk_Representation_UncondConvexRisk

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem expectation_minimalPenalty_eq {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ) (Q : PG m P)
    (Z : Ω → EReal) (hZ : IsEssSup P (penaltyFamily m P ρ Q) Z) :
    HasExpectation P Z ∧
      expectation P Z = minPenalty₀ P (fun X => ∫ ω, ρ X ω ∂P) Q.1 := by sorry

end CondConvexRisk.Representation
