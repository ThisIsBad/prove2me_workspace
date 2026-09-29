import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_marg

namespace OnlinePrimalDual.GroupSteiner

/-- The conditional probability `ℙ[e ∈ C ∣ e' ∈ C]` that edge `e` belongs to the random cover
`C`, given that edge `e'` does (`0` if `ℙ[e' ∈ C] = 0`, matching Lean/Mathlib's `x / 0 = 0`
convention; the algorithm's rule (Algorithm box, p. 230) only ever invokes this quantity with
`e' = parent e` and `marg e' > 0`, since the algorithm never conditions on a zero-probability
event). Used to state the rounding algorithm's third update rule (p. 230, third bullet). -/
noncomputable def RandomCover.condProb {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : RandomCover E) (e e' : E) : ℝ :=
  (∑ C ∈ Finset.univ.filter (fun C => e ∈ C ∧ e' ∈ C), ρ.p C) / ρ.marg e'

end OnlinePrimalDual.GroupSteiner
