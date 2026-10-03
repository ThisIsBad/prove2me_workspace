import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_LagrangianKernel

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.237, Eq. (8.60): the dual objective function,
in `DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- The **dual objective** `g(y) = inf\{K(x,y) : x ∈ Zⱽ\}` (Eq. (8.60)). -/
noncomputable def DualObjective {V U : Type*} [Fintype U]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) (y : U → ℤ) : EReal :=
  sInf {v : EReal | ∃ x : V → ℤ, v = LagrangianKernel F x y}

end DiscreteConvex.ConjugacyDuality.Lagrange
