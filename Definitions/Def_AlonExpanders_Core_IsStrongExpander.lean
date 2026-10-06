import Mathlib
import Definitions.Def_AKSSorting_Core_IsExpander
import Definitions.Def_AlonExpanders_Core_IsIOBipartite

namespace AlonExpanders.Core

/-- Strong `(n, d, c)`-expander (Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), §1,
p. 83): a bipartite graph on inputs `I` and outputs `O` with `|I| = |O| = n`, maximal degree (at
most) `d`, such that for **every** `X ⊆ I`
`|N(X)| ≥ (1 + c (1 - |X|/n)) · |X|`   (1.1),
where `N(X) = AKSSorting.Core.neighbours G X` is the set of vertices adjacent to some vertex of
`X`, and `X` is viewed inside `I ⊕ O` through `Sum.inl`. -/
def IsStrongExpander {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ) (c : ℝ) : Prop :=
  Fintype.card I = n ∧ Fintype.card O = n ∧ IsIOBipartite G ∧ G.maxDegree ≤ d ∧
    ∀ X : Finset I,
      (1 + c * (1 - (X.card : ℝ) / n)) * (X.card : ℝ) ≤
        ((AKSSorting.Core.neighbours G (X.map Function.Embedding.inl)).ncard : ℝ)

end AlonExpanders.Core
