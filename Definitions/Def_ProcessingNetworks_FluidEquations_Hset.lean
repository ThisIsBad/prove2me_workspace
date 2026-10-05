import Mathlib
import Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData

namespace ProcessingNetworks.FluidEquations

/-- `H(j)`, Eq. (7.5): for a buffer `j`, the set of same-pool buffers whose static-buffer-priority
rank (the permutation `σ : Fin I ≃ Fin I`) is at least as high as `j`'s — "at least as high"
meaning `σ i ≤ σ j` on the priority index (a *lower* index value is higher priority, matching the
book's "servers ... give priority to class `i` over class `j`` iff `σ(i) < σ(j)`"). -/
def Hset {I K : ℕ} (dat : QueueingNetworkData I K) (σ : Equiv.Perm (Fin I)) (j : Fin I) :
    Finset (Fin I) :=
  Finset.univ.filter (fun i => dat.p i = dat.p j ∧ σ i ≤ σ j)

end ProcessingNetworks.FluidEquations
