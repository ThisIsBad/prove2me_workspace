import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Proposition 3.7 (Bertsekas & Shreve 1996, p. 51). Let `m` be a model whose mapping is the
minimax mapping `H(x, u, J) = sup_{w ∈ W(x,u)} {g(x, u, w) + α J[f(x, u, w)]}` of Section 2.3.5
(eq. (34) of Chapter 3), where `W(x, u)` is nonempty for `x ∈ S`, `u ∈ U(x)`, `g` maps into
`[−∞, ∞]`, `f` into `S`, and the scalar `α` is positive. Then `H` satisfies F.2, with the
inequality of F.2 holding for the same constant `α`. -/
theorem minimax_F2 {S C W : Type*} (m : Model S C) (Wset : S → C → Set W)
    (g : S → C → W → EReal) (f : S → C → W → S) (α : ℝ) (hα : 0 < α)
    (hW : ∀ x, ∀ u ∈ m.U x, (Wset x u).Nonempty)
    (hH : m.H = minimaxH Wset g f α) :
    m.F2With α := by sorry

end BertsekasShreve.FiniteHorizon

