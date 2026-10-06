import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.96, Eq. (3.51)-style: the indicator function
of a discrete set, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

open Classical in
/-- `δ_S : Zⁿ → \{0,+∞\}`: `0` on `S`, `+∞` off it. -/
noncomputable def IndicatorZ {n : ℕ} (S : Set (Fin n → ℤ)) : (Fin n → ℤ) → WithTop ℝ :=
  fun x => if x ∈ S then (0 : WithTop ℝ) else ⊤

end DiscreteConvex.IntegralConvexityC
