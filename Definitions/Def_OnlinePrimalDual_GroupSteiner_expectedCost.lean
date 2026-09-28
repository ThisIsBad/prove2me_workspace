import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover

namespace OnlinePrimalDual.GroupSteiner

/-- The expected cost `𝔼[∑_{e ∈ C} cₑ]` of the random cover `C` drawn from `ρ`, with respect to
an edge-cost function `c` (Buchbinder & Naor, FnT TCS 2009, Lemma 11.2, p. 230). -/
def RandomCover.expectedCost {E : Type*} [Fintype E] [DecidableEq E] (ρ : RandomCover E)
    (c : E → ℝ) : ℝ :=
  ∑ C, ρ.p C * ∑ e ∈ C, c e

end OnlinePrimalDual.GroupSteiner
