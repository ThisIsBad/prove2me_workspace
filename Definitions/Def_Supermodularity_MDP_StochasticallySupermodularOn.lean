import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 159, Subsection 3.9.1 (the definition preceding Theorem 3.9.1).

"If `T` is a sublattice of `Rᵐ` and `∫_S dF(t,w)` is a supermodular ... function of `t`
on `T` for each increasing set `S` in `Rⁿ`, then `Ftw` is stochastically supermodular
... in `t` on `T`." As in `StochasticallyIncreasingOn`, `μ a S` (converted with
`ENNReal.toReal`) stands for `∫_S dF(a,w)`; callers supply `IsProbabilityMeasure (μ a)`.
-/

namespace Supermodularity.MDP

/-- `StochasticallySupermodularOn D μ` says the family of measures `μ a` on `ℝⁿ`, indexed
by `a` ranging over the domain `D` of a lattice `α`, is stochastically supermodular on
`D`: for every increasing (upward-closed) set `S ⊆ ℝⁿ`, the probability `μ a S` is a
supermodular function of `a` on `D`. -/
def StochasticallySupermodularOn {α : Type*} [Lattice α] {n : ℕ}
    (D : Set α) (μ : α → MeasureTheory.Measure (Fin n → ℝ)) : Prop :=
  ∀ ⦃S : Set (Fin n → ℝ)⦄, IsUpperSet S →
    Supermodularity.Monotonicity.SupermodularOn (fun a => (μ a S).toReal) D

end Supermodularity.MDP
