import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

theorem minimalPenalty_rhoGamma_eq_dv {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) (Q : PG m P) (V : Ω → EReal) :
    IsEssSup P (dvFamily m P Q) V ↔
      IsEssSup P (penaltyFamily m P (rhoGamma m P γ) Q) (fun ω => ((γ⁻¹ : ℝ) : EReal) * V ω) := by sorry

end CondConvexRisk.Entropic
