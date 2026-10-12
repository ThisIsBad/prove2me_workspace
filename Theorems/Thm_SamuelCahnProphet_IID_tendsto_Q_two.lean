import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology

namespace SamuelCahnProphet.IID

theorem tendsto_Q_two :
    Tendsto (fun p : ℝ × ℝ => Q p.1 p.2) ((𝓝[>] (0 : ℝ)) ×ˢ atTop) (𝓝 2) := by sorry

end SamuelCahnProphet.IID

