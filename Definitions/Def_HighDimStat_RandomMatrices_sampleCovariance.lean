import Mathlib

namespace HighDimStat.RandomMatrices

/-- The **sample covariance matrix** `Σ̂ := (1/n) ∑ᵢ xᵢxᵢᵀ`, Wainwright, *High-Dimensional
Statistics* (2019), p. 179 (Corollary 6.20) and p. 181 (Theorem 6.23), for a sample
`x₁,...,xₙ ∈ ℝ^d`. -/
noncomputable def sampleCovariance {n d : ℕ} (x : Fin n → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j k => (1 / (n : ℝ)) * ∑ i, x i j * x i k

end HighDimStat.RandomMatrices
