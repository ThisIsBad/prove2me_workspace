import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Proposition 5 (p. 941): in a reflexive, strictly convex, smooth Banach space, for a
nonempty closed convex `C`, `x ∈ E` and `q = Q_C x`,
`φ(y, Q_C x) + φ(Q_C x, x) ≤ φ(y, x)` for all `y ∈ C` (2.6). -/
theorem prop5_three_point [StrictConvexSpace ℝ E] (hR : IsReflexive E) (hS : IsSmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x) (C : Set E)
    (hne : C.Nonempty) (hcl : IsClosed C) (hcv : Convex ℝ C) (x q : E)
    (hq : IsGenProj J C x q) :
    ∀ y ∈ C, phi J y q + phi J q x ≤ phi J y x := by sorry

end ProximalBanach.Hybrid
