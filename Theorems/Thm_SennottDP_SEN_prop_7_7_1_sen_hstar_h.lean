import Mathlib
import Definitions.Def_SennottDP_SEN_Assumptions

namespace SennottDP.SEN

/-- Sennott (1999), Proposition 7.7.1, p. 158: (SEN) ⇒ (H*) ⇒ (H). With the witnesses made
explicit: if (SEN) holds for `z` with function `Mf` and constant `L`, then (H*) holds for `z`
with `Mf` and the constant function `L(·) = L`; and if (H*) holds for `z` with functions `Mf`,
`Lf`, then (H) holds for `z` with the same `Mf`, `Lf`. -/
theorem prop_7_7_1_sen_hstar_h {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) (z : S) :
    (∀ (Mf : S → ℝ) (L : ℝ), SENAssumptions M z Mf L → HStarAssumptions M z Mf (fun _ => L)) ∧
      ∀ Mf Lf : S → ℝ, HStarAssumptions M z Mf Lf → HAssumptions M z Mf Lf := by sorry

end SennottDP.SEN

