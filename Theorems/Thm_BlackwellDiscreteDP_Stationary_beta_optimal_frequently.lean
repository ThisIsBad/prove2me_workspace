import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- §4, proof of Theorem 5, p. 725 (unnumbered; Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"Let f* be β-optimal for a set of β's having 1 as a limit point."

The proof takes such an `f*` for granted; this states its existence: there is a decision rule
`f*` such that for every `β₀ < 1` some `β ∈ (β₀, 1)` makes `f*^(∞)` β-optimal against all
policies. -/
theorem beta_optimal_frequently {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act) :
    ∃ fstar : St → Act, ∀ β₀ : ℝ, β₀ < 1 →
      ∃ β : ℝ, β₀ < β ∧ β < 1 ∧ M.IsBetaOptimal β (stationary fstar) := by sorry

end BlackwellDiscreteDP.Stationary

