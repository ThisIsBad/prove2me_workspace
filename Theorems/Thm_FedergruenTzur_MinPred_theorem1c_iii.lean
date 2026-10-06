import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList

namespace FedergruenTzur.MinPred

open LotSizing

/-- THEOREM 1(c)(iii), p. 915: if `g(r) = ∞` then `S ∖ {i_r} ⊇ Ω(j)`.
(0-based: `g(r) = gval j L (r - 1)`, `i_r = L[r - 1]`.) -/
theorem theorem1c_iii (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) (hlen : 0 < L.length)
    (hg : P.gval j L (L.length - 1) = ⊤) :
    P.Omega j ⊆ L.toFinset.erase (L.getD (L.length - 1) 0) := by sorry

end FedergruenTzur.MinPred

