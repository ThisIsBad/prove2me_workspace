import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- Theorem 5, p. 725 (Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"There is an optimal policy which is stationary."

"Optimal" is the §4 notion (p. 721): β-optimal for all `β` sufficiently near `1`. One decision
rule `f` and one threshold `β₀ < 1` serve every `β ∈ (β₀, 1)` and every competing policy
`π` (deterministic, Markov, possibly time-dependent): `V_β(f^(∞)) ≧ V_β(π)` coordinatewise. -/
theorem theorem_5 {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act) :
    ∃ f : St → Act, M.IsOptimal (stationary f) := by sorry

end BlackwellDiscreteDP.Stationary

