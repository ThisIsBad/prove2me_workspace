import Mathlib

namespace CooperationGraphs.FairRule

/-- A transferable-utility game on a finite player set. The source indexes values only by
nonempty coalitions. The coordinate at `∅` is ignored by every operation in this mission. -/
abbrev Game (n : ℕ) := Finset (Fin n) → ℝ

end CooperationGraphs.FairRule
