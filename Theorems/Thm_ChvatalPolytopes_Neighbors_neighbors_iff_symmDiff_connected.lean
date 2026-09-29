import Mathlib
import Definitions.Def_ChvatalPolytopes_Neighbors_StablePolytope
import Definitions.Def_ChvatalPolytopes_Neighbors_AreNeighbors

namespace ChvatalPolytopes.Neighbors

/-- **Theorem 6.2** (Chvátal 1975, p. 149). Let `G = (V, E)` be a graph. Let `y, z` be vectors
from `S(G)`; let `Y, Z` be the corresponding stable sets (`Y = {u : y_u = 1}`,
`Z = {u : z_u = 1}`). Then `y` and `z` are neighbors in `P(G)` if and only if the subgraph `H`
of `G` induced by `(Y − Z) ∪ (Z − Y)` is connected. -/
theorem neighbors_iff_symmDiff_connected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (y z : V → ℝ) (hy : y ∈ stableVectors G) (hz : z ∈ stableVectors G) :
    AreNeighbors G y z ↔
      (G.induce ((onesSet y \ onesSet z) ∪ (onesSet z \ onesSet y))).Connected := by sorry

end ChvatalPolytopes.Neighbors

