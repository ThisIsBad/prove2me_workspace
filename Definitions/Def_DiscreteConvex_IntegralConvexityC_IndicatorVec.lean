import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.94: the {0,1}-indicator vector `χ_Y`, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `χ_Y ∈ Zⁿ`: `1` on `Y`, `0` elsewhere. -/
def IndicatorVec {n : ℕ} (Y : Finset (Fin n)) : Fin n → ℤ :=
  fun i => if i ∈ Y then 1 else 0

end DiscreteConvex.IntegralConvexityC
