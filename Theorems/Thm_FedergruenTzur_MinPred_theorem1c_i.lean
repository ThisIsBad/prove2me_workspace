import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList

namespace FedergruenTzur.MinPred

open LotSizing

/-- THEOREM 1(c)(i), p. 915: if `g(2) ≤ D(j)` then `i_1` may be eliminated, i.e.
`S ∖ {i_1} ⊇ Ω(j)`. (0-based: `g(2) = gval j L 1`, `i_1 = L[0]`.) -/
theorem theorem1c_i (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) (hlen : 1 < L.length)
    (hg : P.gval j L 1 ≤ ((P.D j : ℝ) : EReal)) :
    P.Omega j ⊆ L.toFinset.erase (L.getD 0 0) := by sorry

end FedergruenTzur.MinPred

