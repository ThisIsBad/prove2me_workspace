import Mathlib
import Definitions.Def_ScenarioApproach_EmpiricalCosts_scenarioProgram

namespace ScenarioApproach.EmpiricalCosts

/-- Definition 5.1 (support constraint), for the scenario program (1.4) in its epigraph form
`min_{(ν, t)} t` subject to `t ≥ ℓ(ν, δⱼ)`, `j = 1, …, m`, whose solution is
`(νstar, worstCost ℓ ω νstar)`: the constraint of scenario `i` is a support constraint if its
removal improves the solution, i.e. some `(ν, t)` satisfying every other constraint has
`t < max_j ℓ(νstar, δⱼ)`. -/
def IsSupportConstraint {n m : ℕ} {Δ : Type*} (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    (ω : Fin m → Δ) (νstar : EuclideanSpace ℝ (Fin n)) (i : Fin m) : Prop :=
  ∃ ν : EuclideanSpace ℝ (Fin n), ∃ t : ℝ,
    (∀ j : Fin m, j ≠ i → ℓ ν (ω j) ≤ t) ∧ t < worstCost ℓ ω νstar

/-- The number of support constraints of the scenario program (1.4) with sample `ω` and
solution `νstar`. -/
noncomputable def numSupportConstraints {n m : ℕ} {Δ : Type*}
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ) (ω : Fin m → Δ) (νstar : EuclideanSpace ℝ (Fin n)) :
    ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin m => IsSupportConstraint ℓ ω νstar i).card

/-- Definition 5.4 (fully supported problem), for (1.4) with `ν ∈ ℝ^n`, so that the epigraph form
has `d = n + 1` variables: for every `m ≥ d`, with probability 1 over the sample
`(δ₁, …, δ_m)`, the scenario program has exactly `d` support constraints. -/
def FullySupported {n : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : MeasureTheory.Measure Δ)
    [MeasureTheory.IsProbabilityMeasure P] (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ) : Prop :=
  ∀ m : ℕ, n + 1 ≤ m →
    ∀ᵐ ω ∂(MeasureTheory.Measure.pi fun _ : Fin m => P),
      ∀ ν, IsSolution ℓ ω ν → numSupportConstraints ℓ ω ν = n + 1

end ScenarioApproach.EmpiricalCosts
