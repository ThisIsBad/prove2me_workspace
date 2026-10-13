import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market
import Definitions.Def_MDPFinance_TerminalWealth_PowerAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Theorem 4.2.6 (Bäuerle–Rieder, p. 83, PDF 97). Under Assumption (FM) (`hFM2`), let `U` be
the power utility, `U(x) = x^γ/γ`, `domU = [0,∞)`, `0 < γ < 1`. Then: a) the value functions are
`V_n(x) = d_n x^γ`, `x ≥ 0`, with `d_N = 1/γ` and `d_n = (1/γ) ∏_{k=n}^{N-1} (1+i_{k+1})^γ v_k`;
b) the optimal amounts invested in the stocks are `f_n^*(x) = α_n^* x`, `x ≥ 0`, where `α_n^*`
is the optimal solution of (4.7); the optimal portfolio strategy is `(f_0^*,…,f_{N-1}^*)`. -/
theorem power_utility_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hdomU : M.domU = Set.Ici (0 : ℝ)) (hU : ∀ x ≥ (0 : ℝ), M.U x = x ^ γ / γ) :
    (∀ n ≤ M.N, ∀ x ≥ (0 : ℝ),
        M.V n x = ((((1 / γ) * ∏ k ∈ Finset.Ico n M.N, ((1 + M.i (k + 1)) ^ γ * M.vPower γ k)) *
          x ^ γ : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.Afrac n ∧
          ∫ ω, (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ^ γ ∂M.measIP = M.vPower γ n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x ≥ (0 : ℝ), fstar n x = fun k => αstar n k * x) ∧
          ∀ x ≥ (0 : ℝ), M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.TerminalWealth

