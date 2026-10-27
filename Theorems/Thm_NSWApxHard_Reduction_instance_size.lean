import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Lee, p. 2: for a 3-regular graph on `N` vertices with `k` vertex items, the reduced instance
has `n = N + M = 2.5N` agents and `m = k + M + 3N = k + 4.5N` items. -/
theorem instance_size {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ)
    (hG : IsCubic G) :
    2 * Fintype.card (Agent G) = 5 * N ∧ 2 * Fintype.card (Item G k) = 2 * k + 9 * N := by sorry

end NSWApxHard.Reduction

