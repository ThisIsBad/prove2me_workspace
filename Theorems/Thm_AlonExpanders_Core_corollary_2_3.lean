import Mathlib
import Definitions.Def_AlonExpanders_Core_IsEnlarger
import Definitions.Def_AlonExpanders_Core_IsMagnifier

namespace AlonExpanders.Core

/-- Corollary 2.3 of Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), p. 85: every
`(n, d, ε)`-enlarger is an `(n, d, c)`-magnifier with `c = 2ε/(d + 2ε)`. The hypothesis `0 ≤ ε`
is added: with `d = 0`, `ε = −1` one gets `c = 1`, and an edgeless graph on `n ≥ 2` vertices is an
`(n, 0, −1)`-enlarger but not an `(n, 0, 1)`-magnifier. -/
theorem corollary_2_3 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n d : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hG : IsEnlarger G n d ε) :
    IsMagnifier G n d (2 * ε / ((d : ℝ) + 2 * ε)) := by sorry

end AlonExpanders.Core

