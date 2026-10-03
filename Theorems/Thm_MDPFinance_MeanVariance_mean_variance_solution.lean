import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Theorem 4.6.6 (Bäuerle–Rieder, p. 123, PDF 137) — the goal of this mission. Let `(d_n)` be
as in Eq. (4.34). For the mean-variance problem `(MV)` (under the section's standing Assumption
(FM), carried by the model): a) the value is
`Var^{π^*}_{x_0}[X_N] = (d_0/(1-d_0))(𝔼^{π^*}_{x_0}[X_N] - x_0S⁰_N)^2`, and
`𝔼^{π^*}_{x_0}[X_N] = μ`; b) the optimal portfolio strategy `π^* = (f_0^*,…,f_{N-1}^*)` is
`f_n^*(x) = ((μ-d_0x_0S⁰_N)/(1-d_0) · S⁰_n/S⁰_N - x) C_{n+1}^{-1}𝔼[R_{n+1}]`. -/
theorem mean_variance_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (dseq : ℕ → ℝ) (hdN : dseq M.N = 1)
    (hdrec : ∀ n < M.N, dseq n = dseq (n + 1) * (1 - M.ell (n + 1))) :
    ∃ πstar : ℕ → ℝ → (Fin d → ℝ), M.IsOptimalMV πstar ∧
      M.varXN πstar = (dseq 0 / (1 - dseq 0)) * (M.meanXN πstar - M.x0 * M.S0 M.N) ^ 2 ∧
      M.meanXN πstar = M.μ ∧
      (∀ n < M.N, ∀ x : ℝ, πstar n x =
        fun k => ((M.μ - dseq 0 * M.x0 * M.S0 M.N) / (1 - dseq 0) * (M.S0 n / M.S0 M.N) - x) *
          ((M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1)) k)) := by sorry

end MDPFinance.MeanVariance
