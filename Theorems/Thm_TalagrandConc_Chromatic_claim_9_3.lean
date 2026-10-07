import Mathlib
import Definitions.Def_TalagrandConc_Chromatic_Basic

open MeasureTheory
open scoped Classical

namespace TalagrandConc.Chromatic

theorem claim_9_3 (n m k : ℕ) (t : ℝ) (ht : 0 < t) (a : ℤ) (ω : VxSpace n)
    (hω : ω ∈ setB (setA n m k t a) t) :
    (((a - k : ℤ)) : WithTop ℤ) ≤ chiMZ (vxGraph ω) m := by sorry

end TalagrandConc.Chromatic

