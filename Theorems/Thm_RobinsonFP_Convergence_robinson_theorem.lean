import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 297, Theorem: if `(U, V)` is a vector system for `A`, then
`lim_{t→∞} min U(t)/t = lim_{t→∞} max V(t)/t = v`, the value of the game. -/
theorem robinson_theorem [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V)
    (x : ι → ℝ) (y : κ → ℝ) (v : ℝ) (hsol : IsSolution A x y v) :
    Tendsto (fun t : ℕ => vmin (U t) / t) atTop (𝓝 v) ∧
      Tendsto (fun t : ℕ => vmax (V t) / t) atTop (𝓝 v) := by sorry

end RobinsonFP.Convergence

