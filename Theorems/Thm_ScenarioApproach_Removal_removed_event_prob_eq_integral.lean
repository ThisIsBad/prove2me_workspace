import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Removal_scenarioProgram

open MeasureTheory

namespace ScenarioApproach.Removal

theorem removed_event_prob_eq_integral {d N k : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d))
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    (J : Finset (Fin N)) (hJ : J.card = k)
    (θJ : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθJ : ∀ ω, IsSolutionWithout Θ Θδ c ω J (θJ ω))
    (hθJ_meas : Measurable θJ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure.pi (fun _ : Fin N => P)
        {ω | (∀ i ∈ J, θJ ω ∉ Θδ (ω i)) ∧ ε < ScenarioApproach.Generalization.violation P Θδ (θJ ω)} =
      ∫⁻ α in Set.Ioc ε 1, ENNReal.ofReal (α ^ k)
        ∂(Measure.map (fun ω => ScenarioApproach.Generalization.violation P Θδ (θJ ω)) (Measure.pi (fun _ : Fin N => P))) := by sorry

end ScenarioApproach.Removal

