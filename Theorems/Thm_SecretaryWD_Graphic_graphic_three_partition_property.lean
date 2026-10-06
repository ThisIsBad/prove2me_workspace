import Mathlib
import Definitions.Def_SecretaryWD_Graphic_GraphicMatroid
import Definitions.Def_SecretaryWD_Graphic_RandomPartition

namespace SecretaryWD.Graphic
theorem graphic_three_partition_property {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsPartitionScheme G.edgeFinset (partitionPMF G.edgeFinset) 3 := by sorry
end SecretaryWD.Graphic

