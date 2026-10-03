import Mathlib

/-!
The negation-and-recast map `ℝ ∪ {-∞} → ℝ ∪ {+∞}`, used to add a lower-capacity term to an
upper-capacity term without a `WithTop ℝ`/`WithBot ℝ` type mismatch, in
`DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- Sends `v : ℝ ∪ {-∞}` to `-v : ℝ ∪ {+∞}`: `⊥ ↦ ⊤`, `(r:ℝ) ↦ (-r:ℝ)`. -/
def NegLowerToUpper (v : WithBot ℝ) : WithTop ℝ :=
  WithBot.recBotCoe (⊤ : WithTop ℝ) (fun r : ℝ => ((-r : ℝ) : WithTop ℝ)) v

end DiscreteConvex.NetworkFlows
