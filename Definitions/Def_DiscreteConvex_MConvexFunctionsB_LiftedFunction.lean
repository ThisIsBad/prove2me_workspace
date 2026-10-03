import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.134, Eq. (6.4), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The lift `f̃ : Z^(Ṽ) → R ∪ {+∞}` of `f` to `Ṽ = \{0\} ∪ V` (Eq. (6.4)), `Option V` with
`none` standing for the new element `0`. -/
def LiftedFunction {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) : (Option V → ℤ) → WithTop ℝ :=
  fun x => if x none = -(∑ v : V, x (some v)) then f (fun v => x (some v)) else ⊤

end DiscreteConvex.MConvexFunctionsB
