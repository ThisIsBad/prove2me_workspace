import Mathlib
import Definitions.Def_WeingartenCalc_Fundamental_TensorPower

open MeasureTheory Matrix

namespace WeingartenCalc.Fundamental

theorem integral_eq_averagingOperator_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (hU : Continuous U) (d : ℕ)
    (i j : Fin d → Fin N) :
    ∫ g, ∏ x : Fin d, (U g : Matrix (Fin N) (Fin N) ℂ) (i x) (j x) ∂μ
      = averagingOperator μ U d i j := by sorry

end WeingartenCalc.Fundamental

