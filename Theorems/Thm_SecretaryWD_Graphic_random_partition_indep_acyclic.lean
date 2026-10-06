import Mathlib
import Definitions.Def_SecretaryWD_Graphic_GraphicMatroid
import Definitions.Def_SecretaryWD_Graphic_RandomPartition

namespace SecretaryWD.Graphic
theorem random_partition_indep_acyclic {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ P ∈ (partitionPMF G.edgeFinset).support,
      IsPartitionOf G.edgeFinset P ∧
        ∀ S : Finset (Sym2 V), IsPartIndep P S → IsAcyclicSet S := by sorry
end SecretaryWD.Graphic

