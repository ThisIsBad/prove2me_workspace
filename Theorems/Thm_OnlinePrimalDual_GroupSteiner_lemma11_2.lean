import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_marg
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RoundedTree
import Definitions.Def_OnlinePrimalDual_GroupSteiner_expectedCost

namespace OnlinePrimalDual.GroupSteiner

/-- **Lemma 11.2** (p. 230, PDF p. 141). "The next lemma follows from linearity of expectation":
given Lemma 11.1's marginal guarantee (`hmarg : ∀ e, ρ.marg e = w' e`), the expected cost of the
random cover `C` (drawn from `ρ`) is at most `∑_{e ∈ T} cₑ w'ₑ`, where `w'ₑ` is the weight of
edge `e` at the end of the iteration. -/
theorem lemma11_2 {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E) (ρ : RandomCover E)
    (w' : E → ℝ) (hmarg : ∀ e, ρ.marg e = w' e) :
    ρ.expectedCost tr.cost ≤ ∑ e, tr.cost e * w' e := by sorry

end OnlinePrimalDual.GroupSteiner
