import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Omega
import Definitions.Def_FedergruenTzur_MinPred_RankedList

namespace FedergruenTzur.MinPred

open LotSizing

/-- Appendix, p. 923, the chains (7)–(8): if a ranked list `L = [i_1, …, i_r]` satisfies (6), then
for a potential cumulative demand `x` strictly between consecutive `g`-values the entry `L[m]`
(the paper's `i_{m+1}`, 0-based) is strictly cheaper than every other entry of `L`.
The lower bound is absent for `m = 0` (the paper's case (i), `D(t) < g(2)`) and the upper bound is
absent for `m = r - 1` (case (iii), `D(t) > g(r)`). -/
theorem appendix_chain_strict (P : LotSizing) (j : ℕ) (L : List ℕ) (hL : P.IsRanked j L)
    (h6 : P.Cond6 j L) (m : ℕ) (hm : m < L.length) (x : ℝ)
    (hlow : m = 0 ∨ P.gval j L m < (x : EReal))
    (hup : L.length ≤ m + 1 ∨ (x : EReal) < P.gval j L (m + 1)) :
    ∀ l ∈ L, l ≠ L.getD m 0 → P.potCost j (L.getD m 0) x < P.potCost j l x := by sorry

end FedergruenTzur.MinPred

