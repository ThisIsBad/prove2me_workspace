import Mathlib
import Definitions.Def_MechanismDesign_Correlated_IndepModel

namespace MechanismDesign.Correlated

open MeasureTheory Indep

/-- Börgers, Proposition 6.3 (p.118). With independent types (and at least two agents), for every
direct mechanism that is ex ante budget balanced there is an equivalent direct mechanism that is ex
post budget balanced. -/
theorem exAnte_to_exPost_budget_balance {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, MeasurableSpace (Θ i)] {A : Type*}
    (ρ : ∀ i, Measure (Θ i)) [∀ i, IsProbabilityMeasure (ρ i)] (hN : 2 ≤ Fintype.card ι)
    (M : DirectMechanism ι Θ A) (hM : IsTransferRule ρ M.t) (hBB : IsExAnteBB ρ M) :
    ∃ M' : DirectMechanism ι Θ A, IsTransferRule ρ M'.t ∧ Equivalent ρ M M' ∧ IsExPostBB M' := by sorry

end MechanismDesign.Correlated

