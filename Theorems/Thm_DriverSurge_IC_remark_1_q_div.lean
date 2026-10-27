import Mathlib
import Definitions.Def_DriverSurge_IC_Model

namespace DriverSurge.IC

open Set

/-- Remark 1, bullet 3 (p. 57): `q_{i→j}(u)/u` is strictly decreasing in `u > 0`. -/
theorem remark_1_q_div (P : Primitives) (i : Fin 2) :
    StrictAntiOn (fun u : ℝ => q P i u / u) (Ioi 0) := by sorry

end DriverSurge.IC

