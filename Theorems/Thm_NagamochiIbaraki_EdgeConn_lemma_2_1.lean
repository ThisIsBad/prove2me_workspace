import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn

namespace NagamochiIbaraki.EdgeConn

theorem lemma_2_1
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (F : ℕ → Finset E)
    (hF : ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E →
      IsMaxSpanningForest ends (Finset.univ \ (Finset.Icc 1 (i - 1)).biUnion F) (F i)) :
    ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E → ∀ x y : V,
      min (localEdgeConn ends Finset.univ x y) (i : ℕ∞) ≤
        localEdgeConn ends ((Finset.Icc 1 i).biUnion F) x y := by sorry

end NagamochiIbaraki.EdgeConn
