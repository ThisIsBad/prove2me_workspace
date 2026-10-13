import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_TreeLayout

namespace SingleMachinePrec.IntervalReduction

/-- Claim 1 (p. 662): the minimum vertex cover of `G′` is larger than that of `G` by exactly
`|V| + |E \ E_T|`. -/
theorem claim_1 {N : ℕ} (G : SimpleGraph (Fin N)) (L : TreeLayout G) :
    (GPrime L).vertexCoverNum =
      G.vertexCoverNum + (N : ℕ∞) + (Fintype.card (NonTreeEdge L) : ℕ∞) := by sorry

end SingleMachinePrec.IntervalReduction

