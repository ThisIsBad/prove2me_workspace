import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram

namespace ScenarioApproach.Generalization

/-- Definition 5.1 (support constraint). For the scenario program with constraints
`ω 0, …, ω (m-1)` and solution `θstar`, the constraint `θ ∈ Θ_{δᵢ}` is a support constraint if
removing it improves the solution: the program without constraint `i` has a feasible point
(in `Θ` and in every `Θ_{δⱼ}`, `j ≠ i`) whose cost is strictly smaller than `cᵀθstar`. -/
def IsSupportConstraint {d m : ℕ} {Δ : Type*} (c : EuclideanSpace ℝ (Fin d))
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (ω : Fin m → Δ) (θstar : EuclideanSpace ℝ (Fin d)) (i : Fin m) : Prop :=
  ∃ θ ∈ Θ, (∀ j : Fin m, j ≠ i → θ ∈ Θδ (ω j)) ∧ inner ℝ c θ < inner ℝ c θstar

/-- The number of support constraints of the scenario program with constraints `ω` and
solution `θstar`. -/
noncomputable def numSupportConstraints {d m : ℕ} {Δ : Type*} (c : EuclideanSpace ℝ (Fin d))
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (ω : Fin m → Δ) (θstar : EuclideanSpace ℝ (Fin d)) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin m => IsSupportConstraint c Θ Θδ ω θstar i).card

/-- Definition 5.4 (fully supported problem). The problem `(c, Θ, {Θ_δ}, ℙ)` is fully supported
if for every `m ≥ d`, for `ℙ^m`-almost every sample `(δ₁, …, δ_m)`, the scenario program with
these `m` constraints has exactly `d` support constraints (counted at its solution). -/
def FullySupported {d : ℕ} {Δ : Type*} [MeasurableSpace Δ] (c : EuclideanSpace ℝ (Fin d))
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P] : Prop :=
  ∀ m : ℕ, d ≤ m →
    ∀ᵐ ω ∂(MeasureTheory.Measure.pi fun _ : Fin m => P),
      ∀ θ, IsSolution c Θ Θδ ω θ → numSupportConstraints c Θ Θδ ω θ = d

end ScenarioApproach.Generalization
