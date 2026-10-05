import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- Theorem 1, p. 720 (Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"If π* ≧ (f, π*) for all f ε F, then π* is optimal."

Here "optimal" is the §3 notion at the fixed discount factor `β ∈ [0, 1)`: `V_β(π*) ≧ V_β(π)`
for every policy `π` (`IsBetaOptimal`). `π*` is an arbitrary policy, not necessarily
stationary. -/
theorem theorem_1 {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (πstar : Policy St Act)
    (h : ∀ f : St → Act, M.V β (Policy.cons f πstar) ≤ M.V β πstar) :
    M.IsBetaOptimal β πstar := by sorry

end BlackwellDiscreteDP.Stationary

