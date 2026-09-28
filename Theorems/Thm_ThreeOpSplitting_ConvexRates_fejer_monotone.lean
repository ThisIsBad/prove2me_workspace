import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_ConvexRates_Algorithm

open InnerProductSpace Filter Topology

namespace ThreeOpSplitting.ConvexRates

/-- Corollary 2.1, Part 1, for Algorithm 2 with `λ_k ≡ 1` and `γ ∈ (0, 2β)`: for a fixed point
`z*` of `T`, the distances `‖z^j - z*‖` are nonincreasing. -/
theorem fejer_monotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (h : H → ℝ) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < 2 * β)
    (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g) (hh : IsSmoothConvex β h)
    (proxf proxg : H → H) (hproxf : IsProx γ f proxf) (hproxg : IsProx γ g proxg)
    (z0 zstar : H) (hfix : splittingOp proxf proxg (gradient h) γ zstar = zstar) :
    Antitone (fun j : ℕ => ‖algZ proxf proxg (gradient h) γ z0 j - zstar‖) := by sorry

end ThreeOpSplitting.ConvexRates

