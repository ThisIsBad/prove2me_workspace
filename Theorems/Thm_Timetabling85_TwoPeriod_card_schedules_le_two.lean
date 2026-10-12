import Mathlib
import Definitions.Def_Timetabling85_TwoPeriod_CT4

namespace Timetabling85.TwoPeriod

theorem card_schedules_le_two {m n p : ℕ} (I : CT4Data m n p) (j : Fin n)
    (hj : (Finset.univ.filter fun k => I.cbar j k = true).card ≤ 2) :
    (schedules I j).card ≤ 2 := by sorry

end Timetabling85.TwoPeriod

