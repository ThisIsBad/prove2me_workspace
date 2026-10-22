import Definitions.Def_LeightonRao_Uniform_Dual

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- Corollary 4, pp. 798–799, with the proof's explicit factor `36`. -/
theorem corollary_4 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V)
    (d : V → V → ℝ) (hd : IsDistanceFunction d) :
    (∃ T : Finset V,
      2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ) ∧
      HasRadiusLE N d T (1 / (2 * (Fintype.card V : ℝ) ^ 2))) ∨
    (∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
      ratioCost N U ≤ 36 * totalWeight N d * Real.logb 2 (Fintype.card V : ℝ)) := by sorry

end LeightonRao.Uniform

