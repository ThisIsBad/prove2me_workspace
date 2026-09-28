import Mathlib

namespace HighDimStat.Pca

/-- The Euclidean (`ℓ²`) norm of a vector `v ∈ ℝ^d`, `‖v‖₂ := (∑ⱼ vⱼ²)^{1/2}`, as used throughout
Wainwright, *High-Dimensional Statistics* (2019), Chapter 8 (e.g. Theorem 8.5's error bound
`‖θ̂ − θ*‖₂`). -/
noncomputable def l2Norm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ j, (v j) ^ 2)

end HighDimStat.Pca
