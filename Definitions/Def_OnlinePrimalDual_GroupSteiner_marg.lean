import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover

namespace OnlinePrimalDual.GroupSteiner

/-- The marginal probability `ℙ[e ∈ C]` that a fixed edge `e` belongs to the random cover `C`
drawn from `ρ` (Buchbinder & Naor, FnT TCS 2009, Lemma 11.1, p. 230). -/
def RandomCover.marg {E : Type*} [Fintype E] [DecidableEq E] (ρ : RandomCover E) (e : E) : ℝ :=
  ∑ C ∈ Finset.univ.filter (fun C => e ∈ C), ρ.p C

end OnlinePrimalDual.GroupSteiner
