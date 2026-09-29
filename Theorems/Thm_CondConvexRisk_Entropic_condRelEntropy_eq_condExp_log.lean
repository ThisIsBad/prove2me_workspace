import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

theorem condRelEntropy_eq_condExp_log {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (Q : PG m P) :
    (P[density m P Q | m] =ᵐ[P] 1) ∧
      condRelEntropy m P Q =ᵐ[P] condExpExt m Q.1 (fun ω => Real.log (density m P Q ω)) := by sorry

end CondConvexRisk.Entropic
