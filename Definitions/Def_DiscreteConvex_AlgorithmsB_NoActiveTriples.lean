import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsActiveTriple

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- No active triple exists. -/
def NoActiveTriples {ι : Type*} (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (W : Finset V) :
    Prop :=
  ∀ i u v, ¬ IsActiveTriple I L W i u v

-- ===== The IFF fixing algorithm's certificate (§10.2.3, end) =====

end DiscreteConvex.AlgorithmsB
