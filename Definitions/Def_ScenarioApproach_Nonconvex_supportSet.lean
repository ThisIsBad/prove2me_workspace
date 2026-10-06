import Mathlib
import Definitions.Def_ScenarioApproach_Nonconvex_scenarioProgram

namespace ScenarioApproach.Nonconvex

/-- Definition 8.8 (support set). For the scenario program (8.12) with constraints
`Θ_{δ_{ω 0}}, …, Θ_{δ_{ω (N-1)}}`, the index set `I` is a support set if the program with
all constraints has a (unique) solution `θ`, and the program with only the constraints
indexed by `I` in place has the same solution: `θ` is also its unique solution. -/
def IsSupportSet {Θ Δ : Type*} {N : ℕ} (f : Θ → ℝ) (Θδ : Δ → Set Θ) (ω : Fin N → Δ)
    (I : Finset (Fin N)) : Prop :=
  ∃ θ, IsUniqueSolutionOn f Θδ ω Finset.univ θ ∧ IsUniqueSolutionOn f Θδ ω I θ

end ScenarioApproach.Nonconvex
