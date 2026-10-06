import Mathlib

namespace ScenarioApproach.Nonconvex

/-- Feasible set of program (8.12) with only the constraints indexed by `I` in place:
`⋂_{i ∈ I} Θ_{δᵢ}` inside the generic decision set `Θ`. For `I = Finset.univ` it is the
feasible set of the program with all `N` constraints; for `I = ∅` it is all of `Θ`. -/
def feasibleOn {Θ Δ : Type*} {N : ℕ} (Θδ : Δ → Set Θ) (ω : Fin N → Δ) (I : Finset (Fin N)) :
    Set Θ :=
  {θ | ∀ i ∈ I, θ ∈ Θδ (ω i)}

/-- `θ` is a solution of program (8.12) `min_{θ ∈ Θ} f(θ)` subject to the constraints indexed
by `I`: it is feasible and no feasible point has a smaller cost. -/
def IsSolutionOn {Θ Δ : Type*} {N : ℕ} (f : Θ → ℝ) (Θδ : Δ → Set Θ) (ω : Fin N → Δ)
    (I : Finset (Fin N)) (θ : Θ) : Prop :=
  θ ∈ feasibleOn Θδ ω I ∧ ∀ θ' ∈ feasibleOn Θδ ω I, f θ ≤ f θ'

/-- `θ` is *the* solution of program (8.12) with the constraints indexed by `I`: it is a
solution and every solution equals it. -/
def IsUniqueSolutionOn {Θ Δ : Type*} {N : ℕ} (f : Θ → ℝ) (Θδ : Δ → Set Θ) (ω : Fin N → Δ)
    (I : Finset (Fin N)) (θ : Θ) : Prop :=
  IsSolutionOn f Θδ ω I θ ∧ ∀ θ', IsSolutionOn f Θδ ω I θ' → θ' = θ

end ScenarioApproach.Nonconvex
