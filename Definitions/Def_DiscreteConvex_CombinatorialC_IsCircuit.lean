import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_Boundary
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSimpleCycle
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.84: a circuit, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- `π : A → R` is a **circuit**: `π(a) ∈ \{0,\pm 1\}` for every arc, `∂π = 0` (conservation),
and `supp⁺(π) ∪ supp⁻(π)` forms a simple cycle. -/
def IsCircuit {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
    (src dst : A → V) (pi : A → ℝ) : Prop :=
  (∀ a, pi a = 1 ∨ pi a = 0 ∨ pi a = -1) ∧ (∀ v, Boundary src dst pi v = 0) ∧
    ∃ (k : ℕ) (v : Fin (k + 1) → V) (arcs : Fin (k + 1) → A), IsSimpleCycle src dst k v arcs ∧
      Finset.image arcs Finset.univ = SuppPosR pi ∪ SuppNegR pi

end DiscreteConvex.CombinatorialC
