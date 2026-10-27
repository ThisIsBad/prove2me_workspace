import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory

namespace FragLOB.Collapse

theorem eq_12 {N : ℕ} (M : Market N) (hM : M.Standing) (Q : Fin N → ℝ)
    (hQ : ∀ i, 0 ≤ Q i) (hW : 0 < workload M Q) :
    ∀ i, delay M Q i = workload M Q / (M.mu * M.beta i) := by sorry

end FragLOB.Collapse

