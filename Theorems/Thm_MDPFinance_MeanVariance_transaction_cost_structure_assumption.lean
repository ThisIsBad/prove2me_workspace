import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostOperators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Proposition 4.5.2 (Bäuerle–Rieder, p. 109, PDF 123). The Structure Assumption (SAN) is
satisfied for the transaction-cost model with `IM_n := IM` and `Δ_n := Δ ∩ F_n`: `g_N ∈ IM`;
`v ∈ IM ⟹ T_n v ∈ IM`; every `v ∈ IM` has a maximizer that is a buy/hold/sell decision rule
(4.26). -/
theorem transaction_cost_structure_assumption {Ω : Type*} [MeasurableSpace Ω]
    (M : TransactionCostMarket Ω) :
    IsInIM M.γ (fun x => M.U (x.1 + x.2)) ∧
      (∀ n < M.N, ∀ v : ℝ × ℝ → ℝ, IsInIM M.γ v → IsInIM M.γ (fun x => M.T n v x.1 x.2)) ∧
      (∀ n < M.N, ∀ v : ℝ × ℝ → ℝ, IsInIM M.γ v →
        ∃ f : ℝ × ℝ → ℝ, IsBuyHoldSellRule f ∧ Measurable f ∧
          ∀ x ∈ Estate, f x ∈ M.Arange x.1 x.2 ∧
            ∫ ω, v (M.h x.1 x.2 (f x) * (1 + M.i (n + 1)),
              f x * M.Rtilde (n + 1) ω) ∂M.measIP = M.T n v x.1 x.2) := by sorry

end MDPFinance.MeanVariance
