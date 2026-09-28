import Mathlib

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 159, Subsection 3.9.1 (the definition preceding Theorem 3.9.1).

"If `∫_S dF(t,w)` is an increasing ... function of `t` on `T` for each increasing set
`S` in `Rⁿ`, then `{F(t,w) : t ∈ T}` is stochastically increasing ... in `t` on `T`."
The probability that a random draw from `F(t,·)` lands in an (upward-closed) increasing
set `S` is represented here as a measure `μ a` of `S`, converted to a real number with
`ENNReal.toReal`; this is a faithful reading of "the probability measure of `S` with
respect to the distribution function `F(t,·)`" whenever `μ a` is a probability measure
(so `μ a S ≤ 1 < ⊤` and `.toReal` never collapses an infinite value to `0`) — callers
supply `IsProbabilityMeasure (μ a)` as a hypothesis where they use this definition.
-/

namespace Supermodularity.MDP

/-- `StochasticallyIncreasingOn D μ` says the family of measures `μ a` on `ℝⁿ`
(`n`-dimensional Euclidean coordinate space, represented as `Fin n → ℝ`), indexed by `a`
ranging over `D`, is stochastically increasing on `D`: for every increasing (upward-closed)
set `S ⊆ ℝⁿ`, the probability `μ a S` is a monotone function of `a` on `D`. -/
def StochasticallyIncreasingOn {α : Type*} [Preorder α] {n : ℕ}
    (D : Set α) (μ : α → MeasureTheory.Measure (Fin n → ℝ)) : Prop :=
  ∀ ⦃S : Set (Fin n → ℝ)⦄, IsUpperSet S → MonotoneOn (fun a => (μ a S).toReal) D

end Supermodularity.MDP
