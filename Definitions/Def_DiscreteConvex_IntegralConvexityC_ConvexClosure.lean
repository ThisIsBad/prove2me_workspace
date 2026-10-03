import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.56): the convex closure of a
function on the integer lattice, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- The convex closure `f̄ : Rⁿ → R ∪ {±∞}` of `f : Zⁿ → R ∪ {+∞}` (Eq. (3.56)). -/
noncomputable def ConvexClosure {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (x : Fin n → ℝ) : EReal :=
  sSup {v : EReal | ∃ (p : Fin n → ℝ) (a : ℝ),
    (∀ y : Fin n → ℤ, ((a + ∑ i, p i * (y i : ℝ) : ℝ) : EReal) ≤ WithBot.some (f y)) ∧
    v = ((a + ∑ i, p i * x i : ℝ) : EReal)}

end DiscreteConvex.IntegralConvexityC
