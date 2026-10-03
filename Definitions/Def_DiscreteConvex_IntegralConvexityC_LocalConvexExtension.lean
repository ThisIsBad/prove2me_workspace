import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegralNeighborhood

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.61): the local convex extension, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- The local convex extension `f̃ : Rⁿ → R ∪ {±∞}` (Eq. (3.61)). -/
noncomputable def LocalConvexExtension {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (x : Fin n → ℝ) :
    EReal :=
  sSup {v : EReal | ∃ (p : Fin n → ℝ) (a : ℝ),
    (∀ y ∈ IntegralNeighborhood x, ((a + ∑ i, p i * (y i : ℝ) : ℝ) : EReal) ≤
      WithBot.some (f y)) ∧
    v = ((a + ∑ i, p i * x i : ℝ) : EReal)}

end DiscreteConvex.IntegralConvexityC
