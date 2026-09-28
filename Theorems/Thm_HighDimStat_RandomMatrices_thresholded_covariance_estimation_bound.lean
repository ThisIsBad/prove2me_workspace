import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_thresholdMatrix
import Definitions.Def_HighDimStat_RandomMatrices_adjacencyMatrix
import Definitions.Def_HighDimStat_RandomMatrices_opNorm
import Definitions.Def_HighDimStat_RandomMatrices_sampleCovariance

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices

/-- **Theorem 6.23** (Thresholding-based covariance estimation), Wainwright, *High-Dimensional
Statistics* (2019), p. 181. Let `{xᵢ}` be an i.i.d. sequence of zero-mean random vectors with
covariance matrix `Σ`, and suppose each component `x_{ij}` is sub-Gaussian with parameter at
most `σ`. If `n > log d`, then for any `δ > 0`, the thresholded sample covariance matrix
`Tλn(Σ̂)` with `λn/σ² = 8√(log d/n) + δ` satisfies
`P[|||Tλn(Σ̂)-Σ|||₂ ≥ 2|||A|||₂λn] ≤ 8e^{-(n/16)min{δ,δ²}}`. -/
theorem thresholded_covariance_estimation_bound {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (x : Fin n → Ω → Fin d → ℝ)
    (Sig : Matrix (Fin d) (Fin d) ℝ) (σ : ℝ) (hn0 : 0 < n)
    (hIndep : iIndepFun x Prob)
    (hIdent : ∀ i, IdentDistrib (x i) (x ⟨0, hn0⟩) Prob Prob)
    (hMean0 : ∀ j, ∫ ω, x ⟨0, hn0⟩ ω j ∂Prob = 0)
    (hCov : ∀ j k, ∫ ω, x ⟨0, hn0⟩ ω j * x ⟨0, hn0⟩ ω k ∂Prob = Sig j k)
    (hSubG : ∀ j, ∀ lam' : ℝ, Integrable (fun ω => Real.exp (lam' * x ⟨0, hn0⟩ ω j)) Prob ∧
      ∫ ω, Real.exp (lam' * x ⟨0, hn0⟩ ω j) ∂Prob ≤ Real.exp (σ ^ 2 * lam' ^ 2 / 2))
    (hnd : Real.log d < n)
    (δ : ℝ) (hδ : 0 < δ) (lam : ℝ)
    (hlam : lam / σ ^ 2 = 8 * Real.sqrt (Real.log d / n) + δ) :
    Prob.real {ω | 2 * opNorm (adjacencyMatrix Sig) * lam ≤
      opNorm (thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig)} ≤
      8 * Real.exp (-((n : ℝ) / 16) * min δ (δ ^ 2)) := by sorry

end HighDimStat.RandomMatrices
