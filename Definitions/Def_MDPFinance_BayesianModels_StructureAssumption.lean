import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- The Structure Assumption (SAN) (Bäuerle–Rieder, p. 23, PDF 38, unnumbered), specialized to
a *stationary* model (the same `IM`, `Δ` at every stage, matching the goal Theorem 5.4.10's own
statement of a single `IM`/`Δ` pair rather than a sequence `IM_n`/`Δ_n`): `IM ⊆ IM(E)`, `Δ` a set
of decision rules, `g ∈ IM`, `T` maps `IM` into itself, and every `v ∈ IM` has a maximizer in
`Δ`. Restated from `MDPFinance.Bellman.StructureAssumption` (chunk `02a`) /
`MDPFinance.StructuredModels.StructureAssumption` (chunk `02c`). -/
def StructureAssumptionOf (D : Set (E × A)) (Q : E × A → Measure E) (r : E × A → EReal)
    (g : E → EReal) (β : ℝ) (IM' : Set (E → EReal)) (Δ : Set (E → A)) : Prop :=
  IM' ⊆ IM E ∧
  Δ ⊆ {f | IsDecisionRuleOf D f} ∧
  g ∈ IM' ∧
  (∀ v ∈ IM', Top D Q r β v ∈ IM') ∧
  (∀ v ∈ IM', ∃ f ∈ Δ, IsMaximizerOf D Q r β v f)

end MDPFinance.BayesianModels
