import Definitions.Def_LeightonRao_Uniform_Dual

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- Lemma 5, p. 799, with the proof's explicit factor `6`. -/
theorem lemma_5 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (T : Finset V) (hT : 2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ))
    (hsum : 1 / (2 * (Fintype.card V : ℝ)) ≤ ∑ u ∈ Tᶜ, distFrom N d T u) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
      ratioCost N U ≤ 6 * totalWeight N d := by sorry

end LeightonRao.Uniform

