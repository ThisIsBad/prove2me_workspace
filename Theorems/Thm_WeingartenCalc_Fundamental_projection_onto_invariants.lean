import Mathlib
import Definitions.Def_WeingartenCalc_Fundamental_TensorPower

open MeasureTheory Matrix

namespace WeingartenCalc.Fundamental

theorem projection_onto_invariants
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (hU : Continuous U) (d : ℕ) :
    (averagingOperator μ U d)ᴴ = averagingOperator μ U d ∧
      averagingOperator μ U d * averagingOperator μ U d = averagingOperator μ U d ∧
      LinearMap.range (averagingOperator μ U d).mulVecLin = invariants U d := by sorry

end WeingartenCalc.Fundamental

