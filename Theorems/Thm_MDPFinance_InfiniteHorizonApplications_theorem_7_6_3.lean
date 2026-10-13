import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Casino

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Theorem 7.6.3 (Bäuerle–Rieder, p. 228, PDF 239). If `p \le 1/2`, the bold strategy is
optimal, i.e. it maximizes the probability that the player will reach `B` before going bankrupt. -/
theorem theorem_7_6_3 (Mk : CasinoMarket) (hp : Mk.p ≤ 1 / 2) :
    ∀ x, Mk.Jinfpi Mk.bold x = Mk.Jinf x := by sorry

end MDPFinance.InfiniteHorizonApplications

