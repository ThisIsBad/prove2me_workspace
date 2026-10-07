import Mathlib
import Definitions.Def_MechanismDesign_Correlated_IndepModel

namespace MechanismDesign.Correlated

open MeasureTheory Indep

/-- Börgers, Proposition 6.1 (p.116). With independent types (the prior is the product of the type
distributions `ρ i`), a decision rule `q` is part of a Bayesian incentive-compatible direct mechanism
`(q, t₁, …, t_N)` if and only if `q` is interim cyclically monotone. -/
theorem interim_cyclical_monotonicity {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, MeasurableSpace (Θ i)] {A : Type*} [MeasurableSpace A]
    (ρ : ∀ i, Measure (Θ i)) [∀ i, IsProbabilityMeasure (ρ i)] (u : ∀ i, A → Θ i → ℝ)
    (q : (∀ i, Θ i) → A) (hq : IsDecisionRule ρ u q) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, IsTransferRule ρ t ∧ IsBIC ρ u ⟨q, t⟩) ↔
      IsInterimCyclicallyMonotone ρ u q := by sorry

end MechanismDesign.Correlated

