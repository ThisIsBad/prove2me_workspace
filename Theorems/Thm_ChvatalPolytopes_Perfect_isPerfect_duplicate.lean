import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope
import Definitions.Def_ChvatalPolytopes_Perfect_IsPerfect
import Definitions.Def_ChvatalPolytopes_Perfect_duplicate

namespace ChvatalPolytopes.Perfect

/-- **Lovász's second theorem** (cited in Chvátal 1975, §3, p. 140, from Lovász [16, 15]): a
perfect graph remains perfect after the duplication of an arbitrary vertex `u` (adding a new
vertex `u'` joined to all the neighbours of `u` but not to `u`). "Perfect" is the paper's
α-perfection `IsPerfect`. -/
theorem isPerfect_duplicate {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPerfect G) (u : V) :
    IsPerfect (duplicate G u) := by sorry

end ChvatalPolytopes.Perfect

