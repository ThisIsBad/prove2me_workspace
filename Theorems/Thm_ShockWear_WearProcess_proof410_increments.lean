import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ShockWear.WearProcess

theorem proof410_increments {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ)
    (hZ : IsWearProcess pr Z κ) (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    ∃ κ' : ℕ → Kernel ℝ ℝ, IsDamageSeq pr (wearIncr Z Δ) κ' := by sorry

end ShockWear.WearProcess

