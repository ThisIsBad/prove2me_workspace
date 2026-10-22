import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ShockWear.WearProcess

theorem proof410_passSurv_limit {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (Z : ℝ≥0 → Ω → ℝ) (hZ : IsMonotoneWear pr Z) (x : ℝ) (t : ℝ≥0) :
    Tendsto (fun ε : ℝ≥0 => wearCdf pr Z (t + ε) x) (𝓝[>] 0)
      (𝓝 (passSurv pr Z x (t : ℝ))) := by sorry

end ShockWear.WearProcess

