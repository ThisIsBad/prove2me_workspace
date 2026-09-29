import Mathlib
import Definitions.Def_ChvatalPolytopes_Separation_AlphaCritical
import Definitions.Def_ChvatalPolytopes_Separation_IsCutset

namespace ChvatalPolytopes.Separation

/-- **Corollary 4.3** (Chvátal 1975, p. 144; Berge [3, Corollary 2, Chapter 13, Section 3]).
No complete subgraph of a connected α-critical graph is a cutset.

`K` is any complete vertex set (`G.IsClique K`, not necessarily maximal, possibly empty);
"cutset" is `IsCutset`: two vertices outside `K` not joined by any path of `G − K`. -/
theorem no_clique_cutset_of_alpha_critical {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (hcrit : IsAlphaCritical G)
    (K : Set V) (hK : G.IsClique K) :
    ¬ IsCutset G K := by sorry

end ChvatalPolytopes.Separation

