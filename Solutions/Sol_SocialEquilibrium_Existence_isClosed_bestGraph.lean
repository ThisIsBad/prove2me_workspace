import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

theorem aux_icbg_graph_eq {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) :
    graph (bestSet X A f i) = graph (A i) ∩
      (fun p : Others X i × X i => (f i (join X i p.1 p.2), bestValue X A f i p.1)) ⁻¹'
        {q : EReal × EReal | q.1 = q.2} := by
  ext p
  simp [graph, bestSet]

end SocialEquilibrium.Existence

open SocialEquilibrium.Existence

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι)
    (hG : IsClosed (graph (A i)))
    (hf : ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i)))
    (hφ : Continuous (bestValue X A f i)) :
    IsClosed (graph (bestSet X A f i)) := by
  rw [aux_icbg_graph_eq]
  apply ContinuousOn.preimage_isClosed_of_isClosed
  · exact hf.prodMk (hφ.comp continuous_fst).continuousOn
  · exact hG
  · exact isClosed_diagonal
