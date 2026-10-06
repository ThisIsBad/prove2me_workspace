import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AKSSorting_Core_IsExpander
import Definitions.Def_AlonExpanders_Core_IsIOBipartite

namespace AlonExpanders.Core

/-- Proof of Lemma 3.3 in Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), p. 92, first
inequality of the display (Tanner's bound, [30, Theorem 2.1]): for a `d`-regular bipartite graph
on `I ⊕ O` with `|I| = |O| = n`, every `X ⊆ I` with `α = |X|/n` satisfies
`|N(X)| ≥ d² / (α (d² − (d − λ)²) + (d − λ)²) · |X|`. -/
theorem tanner_bound {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ)
    (hI : Fintype.card I = n) (hO : Fintype.card O = n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) (X : Finset I) :
    (d : ℝ) ^ 2 /
        (((X.card : ℝ) / n) * ((d : ℝ) ^ 2 - ((d : ℝ) - AlonMilman.Diameter.lambda1 G) ^ 2) +
          ((d : ℝ) - AlonMilman.Diameter.lambda1 G) ^ 2) * (X.card : ℝ) ≤
      ((AKSSorting.Core.neighbours G (X.map Function.Embedding.inl)).ncard : ℝ) := by sorry

end AlonExpanders.Core

