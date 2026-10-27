import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory

namespace FragLOB.Collapse

theorem theorem_1 {N : ℕ} (M : Market N) (hM : M.Standing) (F : Measure ℝ)
    [IsProbabilityMeasure F] (hF : F (Set.Iio 0) = 0) (hmean : Integrable (fun γ => γ) F) :
    (∀ (pi : ℝ → Fin (N + 1) → ℝ) (W : ℝ), 0 < W → IsAggOptimal M F W pi →
        AggBalance M F pi → IsEquilibrium M F pi (lift M F pi W)) ∧
      (∀ (pi : ℝ → Fin (N + 1) → ℝ) (Q : Fin N → ℝ), IsEquilibrium M F pi Q →
        IsAggOptimal M F (workload M Q) pi ∧ AggBalance M F pi) := by sorry

end FragLOB.Collapse

