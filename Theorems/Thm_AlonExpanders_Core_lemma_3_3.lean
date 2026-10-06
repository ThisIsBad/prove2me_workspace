import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AlonExpanders_Core_IsIOBipartite
import Definitions.Def_AlonExpanders_Core_IsStrongExpander

namespace AlonExpanders.Core

/-- Lemma 3.3 of Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), p. 92: a `d`-regular
bipartite graph on `I ⊕ O` with `|I| = |O| = n` and `λ = λ(G)` is a strong `(n, d, c)`-expander
with `c = (2dλ − λ²)/d²`. The hypothesis `1 ≤ d` is added: for `d = 0` Lean's `0/0 = 0` gives
`c = 0`, and the empty graph with `n ≥ 1` fails `|N(I)| ≥ |I|`. -/
theorem lemma_3_3 {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ) (hd : 1 ≤ d)
    (hI : Fintype.card I = n) (hO : Fintype.card O = n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) :
    IsStrongExpander G n d
      ((2 * (d : ℝ) * AlonMilman.Diameter.lambda1 G - AlonMilman.Diameter.lambda1 G ^ 2) /
        (d : ℝ) ^ 2) := by sorry

end AlonExpanders.Core

