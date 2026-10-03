import Mathlib

namespace ProcessingNetworks.ProportionalFairness

/-- The group-level aggregate `a_ℓ(x) := ∑_{i ∈ I(ℓ)} x_i` (Eq. 10.22), given a demand-group
assignment `grp : Fin I → Fin L` in place of the book's indicator matrix `G` (an equivalent,
more directly usable encoding of the same partition `{I(ℓ), ℓ ∈ L}`: `Gℓi = 1 ↔ grp i = ℓ`). -/
def groupAggregate {I L : ℕ} (grp : Fin I → Fin L) (x : Fin I → ℝ) (ℓ : Fin L) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => grp i = ℓ), x i

end ProcessingNetworks.ProportionalFairness
