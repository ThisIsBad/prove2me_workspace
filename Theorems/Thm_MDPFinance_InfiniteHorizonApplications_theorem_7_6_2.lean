import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Casino

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Theorem 7.6.2 (Bäuerle–Rieder, p. 227, PDF 238). If `p \ge 1/2`, the timid strategy is
optimal, i.e. it maximizes the probability that the player will reach `B` before going bankrupt. -/
theorem theorem_7_6_2 (Mk : CasinoMarket) (hp : 1 / 2 ≤ Mk.p) :
    ∀ x, Mk.Jinfpi Mk.timid x = Mk.Jinf x := by sorry

end MDPFinance.InfiniteHorizonApplications

