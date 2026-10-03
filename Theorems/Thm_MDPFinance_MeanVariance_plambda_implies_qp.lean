import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Lemma 4.6.3 (Bäuerle–Rieder, p. 120, PDF 134). If `π*` is optimal for `P(λ)`, then `π*` is
optimal for `QP(b)` with `b := 𝔼^{π*}_{x_0}[X_N] + λ`. -/
theorem plambda_implies_qp {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d) (lam : ℝ)
    (πstar : ℕ → ℝ → (Fin d → ℝ)) (hopt : M.IsOptimalPLambda lam πstar) :
    M.IsOptimalQP (M.meanXN πstar + lam) πstar := by sorry

end MDPFinance.MeanVariance
