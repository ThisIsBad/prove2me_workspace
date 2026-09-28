import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 889 (proof of the THEOREM, fourth and fifth displays): if every
`M_ι ⊆ 𝔄̄_ι × 𝔄_ι` is closed, then the graph
`Γ = {(a, a′) | (ā_ι, a′_ι) ∈ M_ι for all ι} = ⋂_ι 𝔐_ι` of the multi-valued function
`a ↦ {a′ | (ā_ι, a′_ι) ∈ M_ι for all ι}` is closed in `𝔄 × 𝔄`. -/
theorem isClosed_graph_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (M : ∀ i : ι, Set (Others X i × X i))
    (hM : ∀ i, IsClosed (M i)) :
    IsClosed (graph fun a : ∀ j, X j =>
      {a' : ∀ j, X j | ∀ i, (others X i a, a' i) ∈ M i}) := by sorry

end SocialEquilibrium.Existence
