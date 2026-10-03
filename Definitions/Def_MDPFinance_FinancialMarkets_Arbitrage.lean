import Mathlib
import Definitions.Def_MDPFinance_FinancialMarkets_DiscreteMarket
import Definitions.Def_MDPFinance_FinancialMarkets_Portfolio

open MeasureTheory ProbabilityTheory

namespace MDPFinance.FinancialMarkets

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {M : DiscreteFinancialMarket Ω d}

/-- Definition 3.1.4 (Bäuerle–Rieder, p. 63, PDF 77). An arbitrage opportunity is a
self-financing portfolio strategy `φ` with `X_0^φ = 0` and `ℙ(X_N^φ ≥ 0) = 1`,
`ℙ(X_N^φ > 0) > 0`, where `X_N^φ` is the terminal wealth `Xminus M.N φ`. -/
def IsArbitrageOpportunity (φ : Portfolio M) : Prop :=
  φ.IsSelfFinancing ∧ (∀ᵐ ω ∂M.measIP, φ.X0 ω = 0) ∧
    M.measIP {ω | 0 ≤ φ.Xminus M.N ω} = 1 ∧ M.measIP {ω | 0 < φ.Xminus M.N ω} > 0

/-- The market `M` has no arbitrage opportunities (Bäuerle–Rieder, p. 63, PDF 77-78, Theorem
3.1.5's part a)). -/
def NoArbitrage (M : DiscreteFinancialMarket Ω d) : Prop :=
  ¬ ∃ φ : Portfolio M, IsArbitrageOpportunity φ

end MDPFinance.FinancialMarkets
