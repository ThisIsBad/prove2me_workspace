import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Theorem 4.2.4 (Bäuerle–Rieder, p. 82, PDF 96). In the terminal wealth model of Section 4.2
(`𝔼‖R_n‖ < ∞`, `hFM2`), let `𝔼 R_n = 0` for `n = 1,…,N`. Then: a) the value functions are given
by `V_n(x) = U(x·S⁰_N/S⁰_n)` for `x ∈ E`; b) the optimal portfolio strategy `(f_0^*,…,f_{N-1}^*)`
is given by `f_n^*(x) ≡ 0` ("invest all the money in the bond"). -/
theorem zero_mean_invest_in_bond {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2)
    (hR_zero_mean : ∀ n, 1 ≤ n → n ≤ M.N → ∀ k, ∫ ω, M.R n ω k ∂M.measIP = 0) :
    (∀ n ≤ M.N, ∀ x ∈ M.domU, M.V n x = (M.U (x * M.S0 M.N / M.S0 n) : EReal)) ∧
      (∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
        (∀ n < M.N, ∀ x, fstar n x = 0) ∧
        ∀ x ∈ M.domU, M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.TerminalWealth
