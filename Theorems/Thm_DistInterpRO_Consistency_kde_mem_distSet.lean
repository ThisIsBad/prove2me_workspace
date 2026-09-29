import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem kde_mem_distSet {m n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (xs : Fin n → Fin m → ℝ) :
    volume.withDensity (fun x => ENNReal.ofReal (kde ε xs x)) ∈
      distSet (fun i => box (xs i) ε) := by sorry

end DistInterpRO.Consistency
