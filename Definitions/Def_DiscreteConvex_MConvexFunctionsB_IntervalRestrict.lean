import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, Eq. (3.55), reused p.143, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The restriction of `f` to the integer interval `[a,b]` with `a, b : V → Z ∪ {±∞}`
(represented as `WithBot (WithTop ℤ)`). -/
noncomputable def IntervalRestrict {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (a b : V → WithBot (WithTop ℤ)) :
    (V → ℤ) → WithTop ℝ :=
  fun x => if (∀ v, a v ≤ ((x v : WithTop ℤ) : WithBot (WithTop ℤ)) ∧
      ((x v : WithTop ℤ) : WithBot (WithTop ℤ)) ≤ b v) then f x else ⊤

end DiscreteConvex.MConvexFunctionsB
