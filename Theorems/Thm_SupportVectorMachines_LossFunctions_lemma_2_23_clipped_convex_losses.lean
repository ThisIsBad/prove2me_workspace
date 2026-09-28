import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_RiskBasics
import Definitions.Def_SupportVectorMachines_LossFunctions_ClassificationLosses

namespace SupportVectorMachines.LossFunctions

/-- Lemma 2.23 (Clipped convex losses), p. 34: let `L : X × Y × ℝ → [0,∞)` be a loss such that
`L(x,y,·)` is convex for every `x,y`, and let `M > 0`. Then `L` can be clipped at `M` if and only
if, for every `x, y`, the function `L(x,y,·) : ℝ → ℝ` has at least one global minimizer in
`[-M,M]`. -/
theorem lemma_2_23_clipped_convex_losses {X : Type*} (L : Loss X)
    (hconv : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (M : ℝ) (hM : 0 < M) :
    CanBeClipped L M ↔ ∀ x y, ∃ t0 ∈ Set.Icc (-M) M, ∀ t, L x y t0 ≤ L x y t := by sorry

end SupportVectorMachines.LossFunctions
