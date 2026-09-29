import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem reprFamily_minimalPenalty_le {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ)
    (α : PG m P → Ω → ENNReal) (hα : IsMinimalPenalty m P ρ α)
    (X : Ω → ℝ) (hX : MemLp X ⊤ P) :
    (∀ Q : PG m P, reprFamily m P α X Q ≤ᵐ[P] fun ω => (ρ X ω : EReal)) ∧
    ∀ W : Ω → EReal, IsEssSup P (reprFamily m P α X) W →
      W ≤ᵐ[P] fun ω => (ρ X ω : EReal) := by sorry

end CondConvexRisk.Representation
