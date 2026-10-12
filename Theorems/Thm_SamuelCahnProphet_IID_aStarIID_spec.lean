import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology

namespace SamuelCahnProphet.IID

theorem aStarIID_spec (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (1 - Real.exp (-b - c)) * (b + aStarIID b c * c) / (b + c) = 1 - Real.exp (-b) ∧
      0 < aStarIID b c ∧ aStarIID b c < 1 := by sorry

end SamuelCahnProphet.IID

