import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_NodeConn_Forest

namespace NagamochiIbaraki.NodeConn

theorem lemma_2_4_b
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → ∀ (i j : ℕ) (u v : V), 1 ≤ i → i < j → j ≤ Fintype.card E →
      (edgeGraph ends (cls (σ k) j)).Reachable u v →
        (edgeGraph ends (cls (σ k) i)).Reachable u v := by sorry

end NagamochiIbaraki.NodeConn
