import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

namespace NagamochiIbaraki.EdgeConn

theorem forest_partition_theorem_2_1
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsCompletedRun ends σ K) :
    (∀ e : E, 1 ≤ (σ K).idx e ∧ (σ K).idx e ≤ Fintype.card E) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E → ∀ x y : V,
      min (localEdgeConn ends Finset.univ x y) (i : ℕ∞) ≤
        localEdgeConn ends (upto (σ K) i) x y) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E →
      (cls (σ K) i).card ≤ Fintype.card V - 1) ∧
    (Function.Injective ends →
      (∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card V - 1 →
        (cls (σ K) i).card ≤ Fintype.card V - i) ∧
      (∀ i : ℕ, Fintype.card V ≤ i → i ≤ Fintype.card E → cls (σ K) i = ∅)) := by sorry

end NagamochiIbaraki.EdgeConn
