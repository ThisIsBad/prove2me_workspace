import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_DomR
import Definitions.Def_DiscreteConvex_AlgorithmsC_SuppPosR
import Definitions.Def_DiscreteConvex_AlgorithmsC_SuppNegR

namespace DiscreteConvex.AlgorithmsC

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Axiom (M-EXC[R]): `f` is a real-domain M-convex function. Proposition 10.41 concludes that
the conjugate scaling `f⟨α⟩` is itself a dual-integral polyhedral M-convex function; the
L♮-convexity of `g_α` is Theorem 7.10 (2) and a lemma of its proof, not the proposition. -/
def MExchangeAxiomR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomR g, ∀ y ∈ DomR g, ∀ u ∈ SuppPosR x y, ∃ v ∈ SuppNegR x y, ∃ alpha0 : ℝ, 0 < alpha0 ∧
    ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ alpha0 →
      g x + g y ≥
        g (fun w => x w - alpha * (if w = u then (1:ℝ) else 0) +
          alpha * (if w = v then (1:ℝ) else 0)) +
        g (fun w => y w + alpha * (if w = u then (1:ℝ) else 0) -
          alpha * (if w = v then (1:ℝ) else 0))

end DiscreteConvex.AlgorithmsC
