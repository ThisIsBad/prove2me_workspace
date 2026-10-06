import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_SBFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_TRFR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LinearWeightR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ArgMinR

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.3 (p.208). A technical bound on the difference of weighted minimizers of a
polyhedral L-convex function. The book's sets are `arg min g[-x]` and `arg min g[-y]`, which in
the `LinearWeightR g p = g(·) - ⟨p, ·⟩` convention are `LinearWeightR g x` and `LinearWeightR g y`;
with the weights negated the statement is false (`g(p) = |p₁ - p₂|`, `x = (1,-1)`, `y = (-1,1)`,
`u = 1` gives minimizer sets `{p₁ ≤ p₂}` and `{q₁ ≥ q₂}`, and the bound fails at `p = (0,5)`,
`q = (5,0)`). -/
theorem lconvex_argmin_difference_bound (g : (V → ℝ) → WithTop ℝ) (hg : SBFR g ∧ TRFR g)
    (x y : V → ℝ) (hx : (ArgMinR (LinearWeightR g x)).Nonempty)
    (hy : (ArgMinR (LinearWeightR g y)).Nonempty)
    (u : V) (hu : y u < x u) :
    ∃ v : V, x v < y v ∧ ∀ p ∈ ArgMinR (LinearWeightR g x),
      ∀ q ∈ ArgMinR (LinearWeightR g y), p v - p u ≤ q v - q u := by sorry

end DiscreteConvex.ConjugacyDualityB

