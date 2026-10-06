import Mathlib
import Definitions.Def_SecretaryWD_Graphic_PartitionSecretary

namespace SecretaryWD.Graphic
theorem partition_property_competitive {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (μ : PMF (Finset (Finset (Sym2 V)))) (α : ℝ)
    (hμ : IsPartitionScheme G.edgeFinset μ α) (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) :
    (∀ P ∈ μ.support, ∀ π : Equiv.Perm (Fin G.edgeFinset.card),
        partitionSecretaryOutput G.edgeFinset v P π ⊆ G.edgeFinset ∧
          IsAcyclicSet (partitionSecretaryOutput G.edgeFinset v P π)) ∧
      OPT G.edgeFinset v ≤ Real.exp 1 * α * expectedAlgValue G.edgeFinset v μ := by sorry
end SecretaryWD.Graphic

