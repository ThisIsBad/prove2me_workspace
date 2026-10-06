import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList

namespace FedergruenTzur.MinPred

open LotSizing

/-- THEOREM 1(c)(ii), p. 915: for `k = 2, …, r - 1`, if `g(k + 1) ≤ g(k)` then
`S ∖ {i_k} ⊇ Ω(j)`. (0-based: `k = m + 1`, `i_k = L[m]`, `g(k) = gval j L m`,
`g(k + 1) = gval j L (m + 1)`, and `k ∈ {2, …, r - 1}` is `1 ≤ m`, `m + 1 < r`.) -/
theorem theorem1c_ii (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) (m : ℕ) (hm : 1 ≤ m)
    (hmr : m + 1 < L.length) (hg : P.gval j L (m + 1) ≤ P.gval j L m) :
    P.Omega j ⊆ L.toFinset.erase (L.getD m 0) := by sorry

end FedergruenTzur.MinPred

