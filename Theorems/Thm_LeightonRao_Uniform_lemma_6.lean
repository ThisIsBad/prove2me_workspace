import Definitions.Def_LeightonRao_Uniform_Dual

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- Lemma 6, p. 800, with the factor `36` from Corollary 4 and Lemma 5. -/
theorem lemma_6 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (hconstraint : SatisfiesDistanceConstraint N d) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
      ratioCost N U ≤ 36 * totalWeight N d * Real.logb 2 (Fintype.card V : ℝ) := by sorry

end LeightonRao.Uniform

