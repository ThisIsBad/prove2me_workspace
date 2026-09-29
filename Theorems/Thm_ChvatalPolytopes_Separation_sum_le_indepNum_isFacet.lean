import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope
import Definitions.Def_ChvatalPolytopes_Separation_IsFacet
import Definitions.Def_ChvatalPolytopes_Separation_AlphaCritical

namespace ChvatalPolytopes.Separation

/-- **Theorem 4.2** (Chvátal 1975, p. 143). Let `G = (V, E)` be a graph and let `E*` be the set of
its critical edges. If `G* = (V, E*)` is connected, then the inequality
`Σ (x_u : u ∈ V) ≤ α(G)` is a facet of `P(G)`.

`G*` is `criticalGraph G`; Mathlib's `Connected` includes `Nonempty V` (for `V = ∅` the
conclusion would be false, since the empty system defines `P(G)`). `α(G) = G.indepNum`, cast
to `ℝ`; the facet notion is the paper's (`IsFacet`: every defining linear system of `P(G)`
contains a positive multiple of the inequality). -/
theorem sum_le_indepNum_isFacet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : (criticalGraph G).Connected) :
    IsFacet (Shared.stablePolytope G) (fun _ => 1) (G.indepNum : ℝ) := by sorry

end ChvatalPolytopes.Separation

