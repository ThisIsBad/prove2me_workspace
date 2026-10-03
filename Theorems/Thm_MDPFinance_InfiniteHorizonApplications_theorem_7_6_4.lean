import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Casino

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Theorem 7.6.4 (Bäuerle–Rieder, p. 229, PDF 240). If `p = 1/2`, then the maximal probability
that the player will reach `B` before going bankrupt is given by `J_\infty(x) = x/B`, `x \in E`,
and every stationary strategy `(f,f,\dots)` with `f(x) > 0` for `x > 0` is optimal. -/
theorem theorem_7_6_4 (Mk : CasinoMarket) (hp : Mk.p = 1 / 2) :
    (∀ x : Fin (Mk.B + 1), Mk.Jinf x = (x.1 : ℝ) / Mk.B) ∧
      ∀ f : Fin (Mk.B + 1) → ℕ, (∀ x : Fin (Mk.B + 1), 0 < x.1 → 0 < f x) →
        ∀ x, Mk.Jinfpi f x = Mk.Jinf x := by sorry

end MDPFinance.InfiniteHorizonApplications
