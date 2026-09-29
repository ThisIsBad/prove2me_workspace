import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_NodeConn_Forest

namespace NagamochiIbaraki.NodeConn

theorem lemma_2_2
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → ∀ (v : V) (i : ℕ), 1 ≤ i → i ≤ Fintype.card E →
      ((∃ e : E, v ∈ ends e ∧ (σ k).idx e = i) ↔ i ≤ (σ k).r v) := by sorry

end NagamochiIbaraki.NodeConn
