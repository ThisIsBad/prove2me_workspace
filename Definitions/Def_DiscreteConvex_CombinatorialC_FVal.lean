import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsFeasibleCirc

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83, citing the maximum weight circulation
value, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- `FVal src dst w c` is the maximum weight `F(w,c) = max\{⟨w,ξ⟩ : ξ\text{ a feasible
circulation for } c\}` of a feasible circulation, taken as a real supremum. -/
noncomputable def FVal {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V] (src dst : A → V)
    (w c : A → ℝ) : ℝ :=
  sSup {t : ℝ | ∃ xi : A → ℝ, IsFeasibleCirc src dst c xi ∧ t = dotProduct w xi}

end DiscreteConvex.CombinatorialC
