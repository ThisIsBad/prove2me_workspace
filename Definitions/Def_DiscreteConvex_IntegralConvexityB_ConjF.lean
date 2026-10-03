import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101, Eq. (3.26): the Legendre-Fenchel
transform (convex conjugate), in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- The **convex conjugate** `f•(p) = sup_x \{⟨p,x⟩ - f(x)\}` (Eq. (3.26)). -/
noncomputable def ConjF {V : Type*} [Fintype V] (f : (V → ℝ) → EReal) (p : V → ℝ) : EReal :=
  sSup {v : EReal | ∃ x : V → ℝ, v = ((dotProduct p x : ℝ) : EReal) - f x}

end DiscreteConvex.IntegralConvexityB
