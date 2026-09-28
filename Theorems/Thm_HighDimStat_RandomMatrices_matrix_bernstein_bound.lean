import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_BernsteinConditionMatrix
import Definitions.Def_HighDimStat_RandomMatrices_matrixVariance
import Definitions.Def_HighDimStat_RandomMatrices_opNorm

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices

noncomputable instance instMeasurableSpaceMatrix {d : ℕ} :
    MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) := by
  unfold Matrix; infer_instance

/-- **Theorem 6.17** (Bernstein bound for random matrices), Wainwright, *High-Dimensional
Statistics* (2019), p. 176. Let `{Qᵢ}` be independent, zero-mean, symmetric random matrices
satisfying the Bernstein condition with parameter `b > 0`. Then for all `δ ≥ 0`, the operator
norm satisfies
`P[(1/n)|||∑Qᵢ|||₂ ≥ δ] ≤ 2 rank(∑var(Qᵢ)) exp(-nδ²/(2(σ²+bδ)))`, where
`σ² := (1/n)|||∑var(Qᵢ)|||₂`. -/
theorem matrix_bernstein_bound {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (Q : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ) (b : ℝ) (hb : 0 < b)
    (hIndep : iIndepFun Q Prob)
    (hBernstein : ∀ i, BernsteinConditionMatrix (Q i) Prob b)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    Prob.real {ω | δ ≤ opNorm (∑ i, Q i ω) / (n : ℝ)} ≤
      2 * (Matrix.rank (∑ i, matrixVariance (Q i) Prob) : ℝ) *
        Real.exp (-((n : ℝ) * δ ^ 2) /
          (2 * ((1 / (n : ℝ)) * opNorm (∑ i, matrixVariance (Q i) Prob) + b * δ))) := by sorry

end HighDimStat.RandomMatrices
