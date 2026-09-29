import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem minimalPenalty_minimal {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ)
    (αstar : PG m P → Ω → ENNReal) (hstar : IsMinimalPenalty m P ρ αstar) :
    (∀ α : PG m P → Ω → ENNReal, IsPenaltyFor m P ρ α →
      ∀ Q : PG m P, αstar Q ≤ᵐ[P] α Q) ∧
    ∀ Q : PG m P,
      IsEssSup P
        (fun X : {X : Ω → ℝ // MemLp X ⊤ P ∧ ρ X ≤ᵐ[P] 0} =>
          fun ω => ((-(Q.1[X.1 | m]) ω : ℝ) : EReal))
        (fun ω => (αstar Q ω : EReal)) := by sorry

end CondConvexRisk.Representation
