import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint

namespace ScenarioApproach.Generalization

/-- Theorem 5.2 with footnote 15 (p. 57): if `Θ` and every `Θ_δ` are convex, then for every
`m` and every sample `ω : Fin m → Δ`, the scenario program with these `m` constraints has at most
`d` support constraints at any of its solutions. -/
theorem card_support_constraints_le_dim {d m : ℕ} {Δ : Type*}
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ) (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ))
    (ω : Fin m → Δ) (θstar : EuclideanSpace ℝ (Fin d)) (hθstar : IsSolution c Θ Θδ ω θstar) :
    numSupportConstraints c Θ Θδ ω θstar ≤ d := by sorry

end ScenarioApproach.Generalization

