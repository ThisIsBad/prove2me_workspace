import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- Corollary, p. 721 (Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"There is an optimal policy which is stationary."

Here "optimal" is the §3 notion at a fixed `β ∈ [0, 1)`: there is a decision rule `f` whose
stationary policy `f^(∞)` satisfies `V_β(f^(∞)) ≧ V_β(π)` for every policy `π` (deterministic,
Markov, possibly time-dependent). The §4 statement with the same words is Theorem 5. -/
theorem corollary {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ f : St → Act, M.IsBetaOptimal β (stationary f) := by sorry

end BlackwellDiscreteDP.Stationary

