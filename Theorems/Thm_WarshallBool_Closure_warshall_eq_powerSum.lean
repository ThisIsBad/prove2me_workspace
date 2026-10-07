import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm96
import Definitions.Def_WarshallBool_Closure_Setting

namespace WarshallBool.Closure

/-- Warshall (1962), p. 11, introduction display with the THEOREM ("We assert M* = M′") and
footnote 2: Warshall's construction `M*` (steps 0–4) equals `M ∨ M^2 ∨ ⋯ ∨ M^d`. -/
theorem warshall_eq_powerSum {d : ℕ} (M : Fin d → Fin d → Bool) :
    FloydAlgorithms.ShortestPath.algorithm96 M = powerSum M := by sorry

end WarshallBool.Closure

