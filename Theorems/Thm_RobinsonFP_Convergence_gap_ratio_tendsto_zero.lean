import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 301, proof of the Theorem: `lim_{t→∞} (max V(t) − min U(t))/t = 0`. -/
theorem gap_ratio_tendsto_zero [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) :
    Tendsto (fun t : ℕ => (vmax (V t) - vmin (U t)) / t) atTop (𝓝 0) := by sorry

end RobinsonFP.Convergence

