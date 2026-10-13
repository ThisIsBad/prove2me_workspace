import Mathlib

namespace ScenarioApproach.Generalization

/-- Feasible set of the scenario program (3.3) with the `m` sampled constraints
`ω 0, …, ω (m-1)`: `Θ ∩ ⋂ᵢ Θ_{δᵢ}`. For `m = 0` it is `Θ`. -/
def feasibleSet {d m : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) (ω : Fin m → Δ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Θ ∩ ⋂ i, Θδ (ω i)

/-- `θ` is a solution of the scenario program (3.1)/(3.3) `min_{θ ∈ Θ} cᵀθ` subject to
`θ ∈ ⋂ᵢ Θ_{δᵢ}`: it is feasible and no feasible point has a smaller cost. -/
def IsSolution {d m : ℕ} {Δ : Type*} (c : EuclideanSpace ℝ (Fin d))
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (ω : Fin m → Δ) (θ : EuclideanSpace ℝ (Fin d)) : Prop :=
  θ ∈ feasibleSet Θ Θδ ω ∧ ∀ θ' ∈ feasibleSet Θ Θδ ω, inner ℝ c θ ≤ inner ℝ c θ'

end ScenarioApproach.Generalization
