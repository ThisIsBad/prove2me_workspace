import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.145, Theorem 6.19, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Theorem 6.19 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.145). See the item's
`natural_language_statement` for the full statement. -/
theorem mnat_convex_supermodular {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    ∀ x y : V → ℤ, f x + f y ≤ f (fun v => max (x v) (y v)) + f (fun v => min (x v) (y v)) := by sorry

end DiscreteConvex.MConvexFunctionsB
