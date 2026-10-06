import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList

namespace FedergruenTzur.MinPred

open LotSizing

/-- THEOREM 1(b), p. 915: if a ranked list `L = [i_1, …, i_r]` of periods in `{1, …, j}` contains
`Ω(j)` and satisfies (6), then its first entry `i_1` is an optimal last setup period for the horizon
`j`, i.e. `F(i_1, j) = F(j)` (the paper's `i_1 = l(j)`). -/
theorem theorem1b_first_optimal (P : LotSizing) (j : ℕ) (hj : 1 ≤ j) (L : List ℕ)
    (hL : P.IsRanked j L) (hΩ : P.Omega j ⊆ L.toFinset) (h6 : P.Cond6 j L) :
    ∃ i₁, L.head? = some i₁ ∧ P.Flast i₁ j = P.Fopt j := by sorry

end FedergruenTzur.MinPred

