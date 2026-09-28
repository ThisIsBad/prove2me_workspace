import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Construction

namespace ResourceScheduling.Graph

/-- p. 15: in the constructed instance, two distinct jobs `J_j, J_k` can be executed
simultaneously (the set `{j, k}` satisfies every resource constraint) if and only if the vertices
`j, k` are adjacent. The machine environment plays no role. -/
theorem pair_resourceFeasible_iff_adj {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (y m : ℕ) (q : Fin m → ℝ) (hq : ∀ i, 0 < q i) (j k : Fin N) (hjk : j ≠ k) :
    ((construct G y).toInstance m q hq).ResourceFeasibleSet {j, k} ↔ G.Adj j k := by sorry

end ResourceScheduling.Graph
