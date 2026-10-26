import Definitions.Def_ChanceDetEquiv_PModel_Model

namespace ChanceDetEquiv.PModel

open MeasureTheory

/-- The feasible set of the transformed P-model program (39), including t = 0, is convex. -/
theorem convex_39 {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) [IsProbabilityMeasure d.P]
    (hm : 0 < m) (hn : 0 < n)
    (hMoments : MomentAssumptions d) (hNormal : NormalRows d)
    (hConfidence : Confidence d) :
    Convex ℝ (feasible39 d) := by sorry

end ChanceDetEquiv.PModel

