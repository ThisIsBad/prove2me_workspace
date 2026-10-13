import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market
import Definitions.Def_MDPFinance_TerminalWealth_ExpAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Theorem 4.2.15 (Bäuerle–Rieder, p. 91, PDF 105). Let `U` be the exponential utility,
`U(x) = -exp(-γx)/γ`, `γ > 0`, `domU = ℝ` (no integrability assumption on `R` is needed, only
the model's no-arbitrage assumption). Then: a) the value functions are
`V_n(x) = d_n exp(-γ(S⁰_N/S⁰_n)x)`, `x ∈ ℝ`, with `d_N = -1/γ` and
`d_n = (-1/γ) ∏_{k=n}^{N-1} v_k` (`v_k` the value of problem (4.13)); b) the optimal amounts
invested in the stocks are `f_n^*(x) = a_n^*`, `x ∈ ℝ`, where `a_n^*` is the optimal solution
of (4.13) and does not depend on `x`; the policy `(f_0^*,…,f_{N-1}^*)` is optimal. -/
theorem exponential_utility_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (γ : ℝ) (hγ : 0 < γ) (hdomU : M.domU = Set.univ)
    (hU : ∀ x : ℝ, M.U x = -Real.exp (-γ * x) / γ) :
    (∀ n ≤ M.N, ∀ x : ℝ,
        M.V n x = ((((-1 / γ) * ∏ k ∈ Finset.Ico n M.N, M.vExp γ k) *
          Real.exp (-γ * (M.S0 M.N / M.S0 n) * x) : ℝ) : EReal)) ∧
      (∃ astar : ℕ → (Fin d → ℝ),
        (∀ n < M.N,
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 n) *
            ∑ k, astar n k * M.R (n + 1) ω k)) ∂M.measIP).toReal = M.vExp γ n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x : ℝ, fstar n x = astar n) ∧
          ∀ x : ℝ, M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.TerminalWealth

