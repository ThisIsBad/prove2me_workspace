import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- §2, p. 478, item 3 (convexity clause), for the functions `f_n` of (7): every `f_n` is convex. -/
theorem fLag_convex (M : Model) (n : ℕ) : ConvexOn ℝ univ (M.fLag n) := by sorry

end ClarkScarf.Serial

