import Mathlib

namespace ScenarioApproach.Removal

/-- Feasible set of the scenario program (3.1)/(3.3) with the sample `ω = (δ_1, …, δ_m)`:
`Θ ∩ ⋂_{i} Θ_{δ_i}`. -/
def feasibleSet {d : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) {m : ℕ} (ω : Fin m → Δ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Θ ∩ ⋂ i, Θδ (ω i)

/-- `θ` is a solution of the scenario program (3.1)/(3.3) with sample `ω`: it is feasible and
minimizes the linear cost `⟪c, ·⟫` over the feasible set. -/
def IsSolution {d : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) {m : ℕ}
    (ω : Fin m → Δ) (θ : EuclideanSpace ℝ (Fin d)) : Prop :=
  θ ∈ feasibleSet Θ Θδ ω ∧ ∀ θ' ∈ feasibleSet Θ Θδ ω, inner ℝ c θ ≤ inner ℝ c θ'

/-- Feasible set of the program (5.9): the scenario program with sample `ω = (δ_1, …, δ_N)`
without the constraints whose index lies in `I`, i.e. `Θ ∩ ⋂_{i ∉ I} Θ_{δ_i}`. -/
def feasibleSetWithout {d : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) {N : ℕ} (ω : Fin N → Δ) (I : Finset (Fin N)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Θ ∩ ⋂ (i : Fin N) (_ : i ∉ I), Θδ (ω i)

/-- `θ` is a solution of program (5.9): feasible for the constraints with index outside `I`, and
a minimizer of `⟪c, ·⟫` over that feasible set. -/
def IsSolutionWithout {d : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) {N : ℕ}
    (ω : Fin N → Δ) (I : Finset (Fin N)) (θ : EuclideanSpace ℝ (Fin d)) : Prop :=
  θ ∈ feasibleSetWithout Θ Θδ ω I ∧
    ∀ θ' ∈ feasibleSetWithout Θ Θδ ω I, inner ℝ c θ ≤ inner ℝ c θ'

/-- Assumption 3.4 (convexity): `Θ` and every `Θ_δ` are convex and closed. -/
def ConvexClosedConstraints {d : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Convex ℝ Θ ∧ IsClosed Θ ∧ ∀ δ, Convex ℝ (Θδ δ) ∧ IsClosed (Θδ δ)

/-- Assumption 3.6 (existence and uniqueness): for every `m` and every sample
`(δ_1, …, δ_m)`, the scenario program with these `m` constraints has exactly one solution. -/
def ExistsUniqueSolution {d : ℕ} {Δ : Type*} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ (m : ℕ) (ω : Fin m → Δ), ∃! θ, IsSolution Θ Θδ c ω θ

end ScenarioApproach.Removal
