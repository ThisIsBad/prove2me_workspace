import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 890, step (α) of the proof of the Remark: if `A_ι` has non-void values
and a compact graph `G_ι` and `f_ι` is continuous on `G_ι` (values in the completed real line),
then `φ_ι` is upper semicontinuous at every `ā⁰_ι`. -/
theorem bestValue_upperSemicontinuousAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) (ā₀ : Others X i)
    (hA : ∀ ā : Others X i, (A i ā).Nonempty)
    (hG : IsCompact (graph (A i)))
    (hf : ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i))) :
    UpperSemicontinuousAt (bestValue X A f i) ā₀ := by sorry

end SocialEquilibrium.Existence
