import Mathlib

open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.Convergence

/-- Weak convergence `u k ⇀ x` in a real inner product space:
`⟪u k, y⟫ → ⟪x, y⟫` for every `y`. -/
def WeakTendsto {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℕ → H) (x : H) : Prop :=
  ∀ y : H, Tendsto (fun k => ⟪u k, y⟫_ℝ) atTop (𝓝 ⟪x, y⟫_ℝ)

end ThreeOpSplitting.Convergence
