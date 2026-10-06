import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.88: a totally unimodular matrix, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `A` is **totally unimodular**: every minor (determinant of a square submatrix formed by
choosing any `k` rows and any `k` columns via injective index maps) equals `0`, `1`, or `-1`. -/
def IsTotallyUnimodular {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
    (A : Matrix W V ℝ) : Prop :=
  ∀ (k : ℕ) (rs : Fin k → W) (cs : Fin k → V), Function.Injective rs → Function.Injective cs →
    (A.submatrix rs cs).det = 0 ∨ (A.submatrix rs cs).det = 1 ∨ (A.submatrix rs cs).det = -1

end DiscreteConvex.IntegralConvexityB
