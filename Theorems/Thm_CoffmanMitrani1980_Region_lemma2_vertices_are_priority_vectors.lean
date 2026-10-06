import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset

namespace CoffmanMitrani1980.Region

/-- **Lemma 2** of Coffman and Mitrani, Operations Research 28 (1980), p. 817 (PDF 9): "Let H\*\* be
the set of performance vectors which satisfy the conservation law (1) and the 2^M − 2 inequalities (4),
where g runs through all the proper nonempty subsets of {1, 2, ···, M}. Then, every vertex of H\*\*
coincides with one of the preemptive priority vectors P(1, 2, ···, M), ···, P(M, M − 1, ···, 1)."

**Formalization Note.** "Vertex" is read as an extreme point (`Set.extremePoints ℝ`); for a
polyhedron this is the same as a basic solution, the view of the paper's proof. -/
theorem lemma2_vertices_are_priority_vectors {M : ℕ} (p : Params M) :
    ∀ W ∈ Set.extremePoints ℝ p.Hss, ∃ π : Equiv.Perm (Fin M), W = p.prioVec π := by sorry

end CoffmanMitrani1980.Region

