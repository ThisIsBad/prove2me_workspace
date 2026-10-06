import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList

namespace FedergruenTzur.MinPred

open LotSizing

/-- THEOREM 1(a), p. 915 (Main theorem: Characterization of the Minimal Optimal Predecessors lists).
Fix `j ≥ 1` and let `L = [i_1, …, i_r]` list a set `S` with `Ω(j) ⊆ S ⊆ {1, …, j}`, ranked in
nonascending order of `C̃`, ties in ascending period index. Then `S = Ω(j)` if and only if
`g(1) < g(2) < ⋯ < g(r) < ∞` (condition (6)). -/
theorem theorem1_characterization (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) :
    L.toFinset = P.Omega j ↔ P.Cond6 j L := by sorry

end FedergruenTzur.MinPred

