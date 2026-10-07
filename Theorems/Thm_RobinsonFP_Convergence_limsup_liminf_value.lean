import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 301, proof of the Theorem: `lim sup_{t→∞} min U(t)/t ≤ v` and
`lim inf_{t→∞} max V(t)/t ≥ v`, where `v` is the value of the game, stated in ε-form. -/
theorem limsup_liminf_value [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V)
    (x : ι → ℝ) (y : κ → ℝ) (v : ℝ) (hsol : IsSolution A x y v) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop,
      vmin (U t) / t ≤ v + ε ∧ v - ε ≤ vmax (V t) / t := by sorry

end RobinsonFP.Convergence

