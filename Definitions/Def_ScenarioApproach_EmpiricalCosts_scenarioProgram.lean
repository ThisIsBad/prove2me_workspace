import Mathlib

namespace ScenarioApproach.EmpiricalCosts

/-- The worst-case cost `max_{i=1,…,m} ℓ(ν, δᵢ)` of the decision `ν` on the sample
`ω 0, …, ω (m-1)`, the objective of the scenario program (1.4). For `m ≥ 1` the supremum is a
maximum over a finite nonempty index set; for `m = 0` it is the junk value `0`, and this mission
only evaluates it for `m ≥ 1`. -/
noncomputable def worstCost {n m : ℕ} {Δ : Type*} (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    (ω : Fin m → Δ) (ν : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ i, ℓ ν (ω i)

/-- `ν` is a solution of the scenario program (1.4) `min_{ν ∈ ℝ^{d-1}} max_{i=1,…,m} ℓ(ν, δᵢ)`
with the sample `ω`: no decision has a smaller worst-case cost. -/
def IsSolution {n m : ℕ} {Δ : Type*} (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    (ω : Fin m → Δ) (ν : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ ν' : EuclideanSpace ℝ (Fin n), worstCost ℓ ω ν ≤ worstCost ℓ ω ν'

end ScenarioApproach.EmpiricalCosts
