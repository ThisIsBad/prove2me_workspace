import Mathlib
import Definitions.Def_ChvatalPolytopes_SeriesParallel_IsSeriesParallel
import Definitions.Def_ChvatalPolytopes_SeriesParallel_deleteIdentify

namespace ChvatalPolytopes.SeriesParallel

/-- Chvátal 1975, p. 151, proof of Theorem 7.1, Case 4: let `u` be a vertex of degree two whose
two neighbours `v`, `w` are not adjacent. Delete `u` and identify its neighbours `v`, `w`. The
resulting graph `G'` is again a series-parallel network. -/
theorem deleteIdentify_isSeriesParallel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsSeriesParallel G)
    (u v w : V) (hvw : v ≠ w) (huv : G.Adj u v) (huw : G.Adj u w)
    (hdeg : G.degree u = 2) (hnadj : ¬ G.Adj v w) :
    IsSeriesParallel (deleteIdentify G u v w) := by sorry

end ChvatalPolytopes.SeriesParallel

