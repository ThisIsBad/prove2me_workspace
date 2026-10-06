import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_Boundary

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, pp.82-83, Eqs. (2.51)-(2.52): a feasible
circulation, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- `ξ` is a **feasible circulation** for capacity `c`: `0 ≤ ξ(a) ≤ c(a)` for every arc
(Eq. (2.51)) and `∂ξ(v) = 0` at every vertex (Eq. (2.52), conservation). -/
def IsFeasibleCirc {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (c xi : A → ℝ) : Prop :=
  (∀ a, 0 ≤ xi a ∧ xi a ≤ c a) ∧ ∀ v, Boundary src dst xi v = 0

end DiscreteConvex.CombinatorialC
