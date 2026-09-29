import Mathlib
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_UncondConvexRisk

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem mem_PG_of_minPenalty0_lt_top {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (hQ : Q ≪ P)
    (hfin : minPenalty₀ P (fun X => ∫ ω, ρ X ω ∂P) Q < ⊤) :
    ∀ A : Set Ω, MeasurableSet[m] A → Q A = P A := by sorry

end CondConvexRisk.Representation
