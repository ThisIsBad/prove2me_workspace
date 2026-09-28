import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_GQVI
import Definitions.Def_ChanPangGQVI_Shared_Projection

open scoped RealInnerProductSpace

namespace ChanPangGQVI.ProjExistence

/-- **Theorem 5.1** (Chan and Pang 1982, p. 220). Let `f` and `K` be point-to-set mappings of
`ℝⁿ` into itself with `K(x)` closed and convex for all `x`. Then `(x*, y*)` solves `GQVI(K, f)`
if and only if `x* = P_{K(x*)}(x* - y*)` and `y* ∈ f(x*)`.

The equation `x* = P_{K(x*)}(x* - y*)` is written relationally, `IsProj (K x*) (x* - y*) x*`
("`x*` is a nearest point of `K(x*)` to `x* - y*`"), so that no junk value of a projection
function enters when `K(x*)` is empty; for a closed convex set the nearest point is unique, so
this is the paper's equation. -/
theorem theorem_5_1 {n : ℕ}
    (K f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hK_closed : ∀ x, IsClosed (K x)) (hK_convex : ∀ x, Convex ℝ (K x))
    (xs ys : EuclideanSpace ℝ (Fin n)) :
    ChanPangGQVI.Shared.IsGQVISolution K f xs ys ↔
      (ChanPangGQVI.Shared.IsProj (K xs) (xs - ys) xs ∧ ys ∈ f xs) := by sorry

end ChanPangGQVI.ProjExistence

