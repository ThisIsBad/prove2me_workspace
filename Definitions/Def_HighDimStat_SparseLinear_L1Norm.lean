import Mathlib

namespace HighDimStat.SparseLinear

/-- The `ℓ¹`-norm of a vector `θ ∈ ℝ^d`, `‖θ‖₁ := ∑ⱼ |θⱼ|`, as used throughout Wainwright,
*High-Dimensional Statistics* (2019), Chapter 7 (e.g. the basis pursuit program (7.9) and the
Lagrangian Lasso (7.18)). -/
noncomputable def l1Norm {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  ∑ j, |θ j|

end HighDimStat.SparseLinear
