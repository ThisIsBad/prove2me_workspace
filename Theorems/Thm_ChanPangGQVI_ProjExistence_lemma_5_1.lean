import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_Projection

namespace ChanPangGQVI.ProjExistence

/-- **Lemma 5.1** (Chan and Pang 1982, p. 220). Suppose that the point-to-set mapping `K` is
continuous (upper and lower semicontinuous, with full neighbourhoods in `ℝⁿ`) at the point `x₀`
and that `K(x)` is a closed and convex set for all `x`. Then for each `y₀` the projection function
`p(x, y) = P_{K(x)}(y)` is continuous at `(x₀, y₀)`.

Implicit hypothesis made explicit: `K(x)` is nonempty for all `x`. The paper's projection
function `p(x, y) = P_{K(x)}(y)` is only defined when `K(x) ≠ ∅`, and its proof picks points
`zᵏ ∈ K(xᵏ)`. -/
theorem lemma_5_1 {n : ℕ}
    (K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hK_upper : UpperHemicontinuousAt K x₀) (hK_lower : LowerHemicontinuousAt K x₀)
    (hK_closed : ∀ x, IsClosed (K x)) (hK_convex : ∀ x, Convex ℝ (K x))
    (hK_nonempty : ∀ x, (K x).Nonempty)
    (y₀ : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ChanPangGQVI.Shared.proj (K p.1) p.2)
      (x₀, y₀) := by sorry

end ChanPangGQVI.ProjExistence

