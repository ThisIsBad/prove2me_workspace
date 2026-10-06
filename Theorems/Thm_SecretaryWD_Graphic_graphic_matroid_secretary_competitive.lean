import Mathlib
import Definitions.Def_SecretaryWD_Graphic_RandomPartition
import Definitions.Def_SecretaryWD_Graphic_PartitionSecretary

namespace SecretaryWD.Graphic
theorem graphic_matroid_secretary_competitive {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) :
    (∀ P ∈ (partitionPMF G.edgeFinset).support, ∀ π : Equiv.Perm (Fin G.edgeFinset.card),
        partitionSecretaryOutput G.edgeFinset v P π ⊆ G.edgeFinset ∧
          IsAcyclicSet (partitionSecretaryOutput G.edgeFinset v P π)) ∧
      OPT G.edgeFinset v ≤
        3 * Real.exp 1 * expectedAlgValue G.edgeFinset v (partitionPMF G.edgeFinset) := by sorry
end SecretaryWD.Graphic

