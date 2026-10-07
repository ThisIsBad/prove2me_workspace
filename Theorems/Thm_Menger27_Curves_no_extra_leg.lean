import Mathlib
import Definitions.Def_Menger27_Curves_Basic

namespace Menger27.Curves

/-- The observation spanning pp. 97–98: order at most `n` excludes `n+1` legs. -/
theorem no_extra_leg {X : Type*} [MetricSpace X]
    (p : X) (n : ℕ) (horder : OrderAtMost p n) :
    ¬ HasNBein p (n + 1) := by sorry

end Menger27.Curves

