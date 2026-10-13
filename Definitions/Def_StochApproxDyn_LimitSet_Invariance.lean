import Mathlib

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Invariance in the sense of Benaïm (1999), p. 20: a set `A` is *invariant* for the semiflow
`Φ` if `Φ_t(A) = A` for every `t ≥ 0` (equality, not mere inclusion). -/
def IsInvariantSet {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (A : Set M) : Prop :=
  ∀ t : ℝ≥0, Φ t '' A = A

/-- The restriction `Φ|Λ` of a semiflow to an invariant set `Λ`, a semiflow on the subtype `↥Λ`
(with the subspace metric). It only uses `Φ_t(Λ) ⊆ Λ`, which follows from invariance. -/
def restrictSemiflow {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) {Λ : Set M}
    (h : IsInvariantSet Φ Λ) : Flow ℝ≥0 Λ :=
  Φ.restrict (fun t _ hx => h t ▸ Set.mem_image_of_mem (Φ t) hx)

/-- The omega limit set of `x` (p. 20): the set of points `p = lim_k Φ_{t_k}(x)` for some
sequence `t_k → ∞`. -/
def omegaLimitSet {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (x : M) : Set M :=
  {p | ∃ τ : ℕ → ℝ≥0, Filter.Tendsto τ Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun k => Φ (τ k) x) Filter.atTop (nhds p)}

end StochApproxDyn.LimitSet
