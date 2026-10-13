import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Removal_scenarioProgram

open MeasureTheory

namespace ScenarioApproach.Removal

theorem violation_event_subset_iUnion {d N k : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d))
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (I : (Fin N → Δ) → Finset (Fin N)) (hIcard : ∀ ω, (I ω).card = k)
    (θk : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθk : ∀ ω, IsSolutionWithout Θ Θδ c ω (I ω) (θk ω))
    (hviol : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => P)), ∀ i ∈ I ω, θk ω ∉ Θδ (ω i))
    (θI : Finset (Fin N) → (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθI : ∀ J ω, IsSolutionWithout Θ Θδ c ω J (θI J ω))
    (ε : ℝ) :
    ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => P)),
      ω ∈ {ω : Fin N → Δ | ε < ScenarioApproach.Generalization.violation P Θδ (θk ω)} →
        ω ∈ ⋃ J ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
          {ω : Fin N → Δ | (∀ i ∈ J, θI J ω ∉ Θδ (ω i)) ∧ ε < ScenarioApproach.Generalization.violation P Θδ (θI J ω)} := by sorry

end ScenarioApproach.Removal

