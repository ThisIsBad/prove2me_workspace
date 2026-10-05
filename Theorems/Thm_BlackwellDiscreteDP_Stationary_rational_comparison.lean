import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- §4, proof of Theorem 5, pp. 725–726 (unnumbered; Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"Then, for every g, V_β(f*) ≧ V_β(g) for a set of β's having 1 as a limit point. Since all
coordinates of V_β(f*) and V_β(g) are rational functions of β, V_β(f*) ≧ V_β(g) for all β near 1."

For decision rules `f*`, `g`: if `V_β(f*^(∞)) ≧ V_β(g^(∞))` (the whole vector) for a set of
`β < 1` having `1` as a limit point, then it holds for all `β` in some interval `(β₀, 1)`. -/
theorem rational_comparison {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act)
    (fstar g : St → Act)
    (h : ∀ β₀ : ℝ, β₀ < 1 → ∃ β : ℝ, β₀ < β ∧ β < 1 ∧
      M.V β (stationary g) ≤ M.V β (stationary fstar)) :
    ∃ β₀ : ℝ, β₀ < 1 ∧ ∀ β : ℝ, β₀ < β → β < 1 →
      M.V β (stationary g) ≤ M.V β (stationary fstar) := by sorry

end BlackwellDiscreteDP.Stationary

