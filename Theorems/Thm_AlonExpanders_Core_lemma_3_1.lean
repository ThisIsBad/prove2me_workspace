import Mathlib
import Definitions.Def_AlonExpanders_Core_IsStrongExpander
import Definitions.Def_AlonExpanders_Core_IsMagnifier

namespace AlonExpanders.Core

/-- Lemma 3.1 of Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), p. 90: a strong
`(n, d, c)`-expander on `I ⊕ O` is a `(2n, d, c/16)`-magnifier. The hypothesis `2 ≤ n` is added:
for `n = 1`, `K₂` is a strong `(1, 1, c)`-expander for every `c` but not a `(2, 1, c/16)`-magnifier
once `c > 16`. -/
theorem lemma_3_1 {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ) (c : ℝ) (hn : 2 ≤ n)
    (hG : IsStrongExpander G n d c) :
    IsMagnifier G (2 * n) d (c / 16) := by sorry

end AlonExpanders.Core

