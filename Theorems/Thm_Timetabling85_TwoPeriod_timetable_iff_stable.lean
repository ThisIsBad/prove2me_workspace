import Mathlib
import Definitions.Def_Timetabling85_TwoPeriod_CT4

namespace Timetabling85.TwoPeriod

theorem timetable_iff_stable {m n p : ℕ} (I : CT4Data m n p) :
    (∃ x : Fin m → Fin n → Fin p → Bool, IsSolution I x) ↔
      ∃ S : Finset (Node I), (conflictGraph I).IsNIndepSet n S := by sorry

end Timetabling85.TwoPeriod

