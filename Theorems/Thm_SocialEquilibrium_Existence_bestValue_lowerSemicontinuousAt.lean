import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_graph
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 890, step (β) of the proof of the Remark: if in addition to the
hypotheses of (α) the multi-valued function `A_ι` is continuous at `ā⁰_ι`, then `φ_ι` is lower
semicontinuous at `ā⁰_ι`. -/
theorem bestValue_lowerSemicontinuousAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) (ā₀ : Others X i)
    (hA : ∀ ā : Others X i, (A i ā).Nonempty)
    (hG : IsCompact (graph (A i)))
    (hf : ContinuousOn (fun p : Others X i × X i => f i (join X i p.1 p.2)) (graph (A i)))
    (hAc : ConstraintContinuousAt A i ā₀) :
    LowerSemicontinuousAt (bestValue X A f i) ā₀ := by sorry

end SocialEquilibrium.Existence
