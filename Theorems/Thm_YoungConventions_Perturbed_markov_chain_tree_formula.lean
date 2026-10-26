import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_InTree

open Finset

namespace YoungConventions.Perturbed

/-- The Markov chain tree formula (Freidlin–Wentzell 1984, Ch. 6, Lemma 3.1), as quoted in the proof
of Lemma 1 (Young 1993, Econometrica 61:57–84, Appendix, p. 79, PDF p. 24).

Let `P′` be the transition matrix of an aperiodic, irreducible Markov chain on the finite set
`X`, and for `z ∈ X` let `p′_z = ∑_{T ∈ 𝒯_z} ∏_{(x,y) ∈ T} P′_{xy}` (`treeWeight`). Then every
`p′_z` is positive, `μ′_z = p′_z / ∑_x p′_x` is a stationary distribution of `P′`, and it is the
unique stationary distribution of `P′`.

**Formalization Note.** Both hypotheses of the page (aperiodic and irreducible) are kept, although
irreducibility alone suffices. The state type is nonempty: on an empty type both conditions
hold vacuously, but no probability distribution can have total mass `1`. `z`-trees are in-trees
(edges point toward `z`), so for two states `p′_1 = P′_{21}` and `p′_2 = P′_{12}`. -/
theorem markov_chain_tree_formula {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (hirr : A.IsIrreducible) (hap : IsAperiodic A) :
    (∀ z, 0 < treeWeight A z) ∧
    IsStationaryDist A (fun z => treeWeight A z / ∑ x, treeWeight A x) ∧
    ∀ ν : X → ℝ, IsStationaryDist A ν → ν = fun z => treeWeight A z / ∑ x, treeWeight A x := by sorry

end YoungConventions.Perturbed

