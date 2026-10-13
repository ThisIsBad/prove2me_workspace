import Mathlib
import Definitions.Def_SennottDP_SEN_Assumptions

namespace SennottDP.SEN

/-- Sennott (1999), Proposition 7.2.4, p. 137: assume that the (SEN) assumptions hold for a
distinguished state `z` (with some function `Mf` in (SEN2) and constant `L` in (SEN3)). Then
(SEN) holds if `z` is replaced by any other state `x`: there are a function `Mx` and a constant
`Lx` for which (SEN1)–(SEN3) hold with distinguished state `x`. -/
theorem prop_7_2_4_sen_any_state {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) (z : S)
    (Mf : S → ℝ) (L : ℝ) (hSEN : SENAssumptions M z Mf L) (x : S) :
    ∃ (Mx : S → ℝ) (Lx : ℝ), SENAssumptions M x Mx Lx := by sorry

end SennottDP.SEN

