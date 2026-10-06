import Mathlib

/-!
The total weight of a perfect matching (Murota, *Discrete Convex Analysis*, SIAM 2003, p.109),
in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- The weight `∑_u c(u, σ u)` of the perfect matching represented by `σ`. -/
noncomputable def MatchingWeight {Vp Vm : Type*} [Fintype Vp] (c : Vp × Vm → WithTop ℝ)
    (sigma : Vp ≃ Vm) : WithTop ℝ :=
  ∑ u, c (u, sigma u)

end DiscreteConvex.IntegralConvexityB
