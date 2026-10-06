import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model
import Definitions.Def_GallegoOzerADI_ZeroSetup_DecreasingDifferences

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 4, Part 4 (p. 1351): for every period `t ∈ {1, …, T}`, `V_t(x, o_t)` has decreasing
differences in `(x, o_t)` (Definition 2). -/
theorem V_decreasingDifferences {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) :
    DecreasingDifferences (fun x o => P.V t x o) := by sorry

end GallegoOzerADI.ZeroSetup

