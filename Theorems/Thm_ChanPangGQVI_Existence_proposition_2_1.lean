import Mathlib
import Definitions.Def_ChanPangGQVI_Existence_GQVI
import Definitions.Def_ChanPangGQVI_Existence_GICP

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, p. 213, Proposition 2.1. For a point-to-point mapping `m`, a cone-valued
mapping `L` and a point-to-set mapping `f` of `ℝⁿ`, the solution sets of `GICP(L, m, f)` and
`GQVI(K, f)` with `K(x) = m(x) + L(x)` (equation (1)) are equal: a pair `(x, y)` solves one problem
if and only if it solves the other. -/
theorem proposition_2_1 {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) → PointedCone ℝ (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))) :
    ∀ x y : EuclideanSpace ℝ (Fin n),
      IsGICPSolution L m f x y ↔ IsGQVISolution (coneTranslate m L) f x y := by sorry

end ChanPangGQVI.Existence

