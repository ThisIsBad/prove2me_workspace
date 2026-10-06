import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- Theorem 4.3.5 (Bäuerle–Rieder, p. 96, PDF 110). In the consumption-investment model of
Section 4.3 (`dom U_c = dom U_p = [0,∞)`, (FM)(ii) `hFM2`), let `𝔼 R_n = 0` for `n = 1,…,N`.
Then the optimal consumption-investment strategy `(f_0^*,…,f_{N-1}^*)`,
`f_n^*(x) = (c_n^*(x),a_n^*(x))`, has `a_n^*(x) ≡ 0` — investing all the money in the bond is the
optimal investment strategy (the optimal consumption `c_n^*` need not be trivial). -/
theorem zero_mean_invest_in_bond_ci {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : ConsumptionInvestmentMarket Ω d) (hdomU : M.domU = Set.Ici (0 : ℝ)) (hFM2 : M.FM2)
    (hR_zero_mean : ∀ n, 1 ≤ n → n ≤ M.N → ∀ k, ∫ ω, M.R n ω k ∂M.measIP = 0) :
    ∃ fstar : ℕ → ℝ → ℝ × (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
      (∀ n < M.N, ∀ x, (fstar n x).2 = 0) ∧
      ∀ x ∈ M.domU, M.Vpi fstar 0 x = M.V 0 x := by sorry

end MDPFinance.ConsumptionInvestment

