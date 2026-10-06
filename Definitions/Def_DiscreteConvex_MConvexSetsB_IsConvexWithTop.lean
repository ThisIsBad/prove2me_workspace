import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ScalarWithTop

/-!
Convexity of an `R ∪ {+∞}`-valued function on `Rⱽ`, used to state Theorem 4.16 (Murota,
*Discrete Convex Analysis*, SIAM 2003, p.111), in `DiscreteConvex.MConvexSetsB`. `WithTop ℝ`
carries no `Module ℝ` structure (there is no consistent scalar action of negative reals on
`⊤`), so convexity is stated directly via `ScalarWithTop` (always applied with nonnegative
weights here) and the native order on `WithTop ℝ`, rather than via `Mathlib`'s `ConvexOn`. -/

namespace DiscreteConvex.MConvexSetsB

/-- `f : Rⱽ → R ∪ \{+∞\}` is **convex**: for every `x, y` and `t ∈ [0,1]`,
`f(tx + (1-t)y) ≤ t • f(x) + (1-t) • f(y)`. -/
def IsConvexWithTop {V : Type*} (f : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x y : V → ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (fun v => t * x v + (1 - t) * y v) ≤ ScalarWithTop t (f x) + ScalarWithTop (1 - t) (f y)

end DiscreteConvex.MConvexSetsB
