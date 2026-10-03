import Mathlib
import Definitions.Def_MDPFinance_FinancialMarkets_DiscreteMarket
import Definitions.Def_MDPFinance_FinancialMarkets_Portfolio
import Definitions.Def_MDPFinance_FinancialMarkets_Arbitrage

open MeasureTheory ProbabilityTheory

namespace MDPFinance.FinancialMarkets

/-- Theorem 3.1.5 (Bäuerle–Rieder, p. 63, PDF 78) — the goal of this mission. Consider an
`N`-period financial market. The following two statements are equivalent: a) there are no
arbitrage opportunities; b) for `n = 0, …, N-1` and for all `Fam n`-measurable `φ_n ∈ ℝ^d` it
holds: `φ_n · R_{n+1} ≥ 0` `ℙ`-a.s. `⇒` `φ_n · R_{n+1} = 0` `ℙ`-a.s. -/
theorem no_arbitrage_iff_local {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : DiscreteFinancialMarket Ω d) :
    NoArbitrage M ↔
      ∀ n < M.N, ∀ φn : Ω → (Fin d → ℝ), (@Measurable Ω (Fin d → ℝ) (M.Fam n) _ φn) →
        (M.measIP {ω | 0 ≤ ∑ k, φn ω k * M.R (n + 1) ω k} = 1 →
          M.measIP {ω | ∑ k, φn ω k * M.R (n + 1) ω k = 0} = 1) := by sorry

end MDPFinance.FinancialMarkets
