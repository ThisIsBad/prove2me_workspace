import Mathlib

namespace HighDimStat.RandomMatrices

/-- The **operator (spectral) norm** `|||M|||₂`, Wainwright, *High-Dimensional Statistics* (2019),
used throughout Chapter 6. Realized as the operator norm of the continuous linear endomorphism of
Euclidean space that `M` induces (`Matrix.toEuclideanCLM`), i.e. the largest singular value of
`M`. -/
noncomputable def opNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

end HighDimStat.RandomMatrices
