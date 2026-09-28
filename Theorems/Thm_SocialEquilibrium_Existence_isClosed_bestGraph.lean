import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 889 (proof of the THEOREM, second and third displays): if the graph
`G_ι` of `A_ι` is closed, `f_ι` is continuous on `G_ι` and `φ_ι` is continuous, then
`M_ι = {(ā_ι, a_ι) | a_ι ∈ M_{ā_ι}} = {(ā_ι, a_ι) ∈ G_ι | f_ι(ā_ι, a_ι) = φ_ι(ā_ι)}` is closed in
`𝔄̄_ι × 𝔄_ι`. -/
theorem isClosed_bestGraph {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι)
    (hG : IsClosed (graph (A i)))
    (hf : ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i)))
    (hφ : Continuous (bestValue X A f i)) :
    IsClosed (graph (bestSet X A f i)) := by sorry

end SocialEquilibrium.Existence
