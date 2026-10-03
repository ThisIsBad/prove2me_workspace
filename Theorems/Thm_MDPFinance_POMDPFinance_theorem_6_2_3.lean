import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_HistPolicy
import Definitions.Def_MDPFinance_POMDPFinance_MeanVariance

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDPFinance

/-- **Theorem 6.2.3** (Bäuerle–Rieder, p. 188, PDF 201, corrected from `statements.jsonl`'s
mis-tagged "p. 186" — the printed-page footer at PDF 201 reads `188`; verified directly, `188 =
201 - 13`, the constant offset for this chapter). For the mean-variance problem `(MV)` with
partial observation it holds: a) The value of `(MV)` is given by `\text{Var}^{\pi^*}_{x_0}[X_N] =
\frac{d_0(Q_0)}{1-d_0(Q_0)}\big(𝔼^{\pi^*}_{x_0}[X_N]-x_0S^0_N\big)^2` where `d_0(Q_0)` is given
in (6.7); note `𝔼^{\pi^*}_{x_0}[X_N] = \mu`. b) For `(x,\rho) \in E_X \times ℙ(E_Y)` let
`f_n^*(x,\rho) := \Big(\frac{\mu - d_0(Q_0)x_0S^0_N}{1-d_0(Q_0)}\frac{S^0_n}{S^0_N} - x\Big)
C_{n+1}(\rho)^{-1}\ell_{n+1}(\rho)`. Then the portfolio strategy `\pi^* = (f_0,\dots,f_{N-1})` is
optimal for `(MV)` where `f_n(h_n) := f_n^*(x_n,\mu_n(\cdot|h_n))`. The construction sets
`b^* := \mu + \lambda^*` with `\lambda^* = (\mu-x_0S^0_N) \, d_0(Q_0)/(1-d_0(Q_0))` (p. 188,
just before the statement) and reuses Theorem 6.2.2's `QP(b^*)` solution at that specific `b`;
`0 < d_0(Q_0) < 1` by Lemma 6.2.1 (under Assumption (FM), the fields of `MeanVarianceMarket`,
not a separate hypothesis), so the constructed `b^*` and the fraction `d_0(Q_0)/(1-d_0(Q_0))`
are well-defined; `x_0 S^0_N < μ` is Assumption (FM)(iv). Variances are `VarPi` (`∞` for a
strategy without finite second moment). -/
theorem theorem_6_2_3 {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : FilterMarket EY d)
    (Fd : FilterOp M) (Mv : MeanVarianceMarket M) (N : ℕ) (x0 μ : ℝ)
    (hμ : x0 * S0 Mv.i N < μ) :
    (let fs : ℕ → ℝ × Measure EY → Fin d → ℝ := fun n xρ =>
        ((μ - dRem M Fd N M.Q0 * x0 * S0 Mv.i N) / (1 - dRem M Fd N M.Q0) *
              (S0 Mv.i n / S0 Mv.i N) - xρ.1) •
          (CRem M Fd (N - n - 1) xρ.2)⁻¹.mulVec (lRem M Fd (N - n - 1) xρ.2)
      let pistar := ofMarkov M Fd Mv.i x0 fs
      EXN M Fd Mv.i pistar N x0 = (μ : EReal) ∧
        IsMVFeasible M Fd Mv.i N x0 μ pistar ∧
        VarPi M Fd Mv.i pistar N x0 =
          ((dRem M Fd N M.Q0 / (1 - dRem M Fd N M.Q0) * (μ - x0 * S0 Mv.i N) ^ 2 : ℝ) : EReal) ∧
        VarMV M Fd Mv.i N x0 μ =
          ((dRem M Fd N M.Q0 / (1 - dRem M Fd N M.Q0) * (μ - x0 * S0 Mv.i N) ^ 2 : ℝ) : EReal) ∧
        VarPi M Fd Mv.i pistar N x0 = VarMV M Fd Mv.i N x0 μ) := by sorry

end MDPFinance.POMDPFinance
