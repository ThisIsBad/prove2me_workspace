import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.79: the typing constraint `f : Rⁿ → R ∪ {+∞}`
(never `-∞`), in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `f` never takes the value `-∞` (the book's typing `f : Rⁿ → R ∪ \{+∞\}`). -/
def NeverBot {V : Type*} (f : (V → ℝ) → EReal) : Prop :=
  ∀ x, f x ≠ ⊥

end DiscreteConvex.IntegralConvexityB
