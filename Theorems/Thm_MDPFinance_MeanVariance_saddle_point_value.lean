import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Lemma 4.6.2 (Bäuerle–Rieder, p. 119, PDF 133). Let `(π^*,λ^*)` be a saddle-point of
`L_{x_0}(π,λ)`. Then the value of `(MV)` is
`inf_{π∈F^N} sup_{λ≥0} L_{x_0}(π,λ) = sup_{λ≥0} inf_{π∈F^N} L_{x_0}(π,λ) = L_{x_0}(π^*,λ^*)`
(the inner suprema and infima taken in `[-∞,∞]`, an infeasible `π` having `sup_λ = +∞`), and `π^*`
is optimal for `(MV)`. -/
theorem saddle_point_value {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (πstar : ℕ → ℝ → (Fin d → ℝ)) (lamstar : ℝ) (hsaddle : M.IsSaddlePoint πstar lamstar) :
    (⨅ π ∈ {π | M.IsAdmissible 0 π}, ⨆ lam ∈ Set.Ici (0 : ℝ), (M.Lagrangian π lam : EReal)) =
        (⨆ lam ∈ Set.Ici (0 : ℝ), ⨅ π ∈ {π | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) ∧
      (⨆ lam ∈ Set.Ici (0 : ℝ), ⨅ π ∈ {π | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) =
        (M.Lagrangian πstar lamstar : EReal) ∧
      M.IsOptimalMV πstar := by sorry

end MDPFinance.MeanVariance
