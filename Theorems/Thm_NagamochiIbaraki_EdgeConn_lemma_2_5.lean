import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

namespace NagamochiIbaraki.EdgeConn

theorem lemma_2_5
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsCompletedRun ends σ K) :
    ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E →
      IsMaxSpanningForest ends
        (Finset.univ.filter (fun e => ¬ (1 ≤ (σ K).idx e ∧ (σ K).idx e ≤ i - 1)))
        (cls (σ K) i) := by sorry

end NagamochiIbaraki.EdgeConn
