import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_ValueDist
import Definitions.Def_CHMSPricing_OpmUniform_SetSystem

namespace CHMSPricing.OpmUniform

open MeasureTheory

/-- A deterministic direct mechanism for single-parameter agents `ι` (§2.1, p. 4): it maps a
reported value profile `v` to an allocation `M(v)` (the set of served agents) and a payment
`πᵢ(v)` for each agent. -/
structure Mechanism (ι : Type*) where
  alloc : (ι → ℝ) → Finset ι
  pay : (ι → ℝ) → ι → ℝ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quasilinear utility of agent `i` with true value `x` when the reported profile is `b`. -/
noncomputable def Mechanism.utility (M : Mechanism ι) (i : ι) (x : ℝ) (b : ι → ℝ) : ℝ :=
  (if i ∈ M.alloc b then x else 0) - M.pay b i

/-- A truthful (dominant-strategy incentive compatible), ex-post individually rational
mechanism respecting the feasibility constraint `J` on the type space, with measurable
allocation events and measurable, integrable payments (standing pin P3). -/
structure IsTruthful (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι) : Prop where
  feasible : ∀ v ∈ typeSpace D, J.Feasible (M.alloc v)
  dsic : ∀ v ∈ typeSpace D, ∀ i, ∀ x' ∈ Set.Icc (D i).lo (D i).hi,
    M.utility i (v i) (Function.update v i x') ≤ M.utility i (v i) v
  ir : ∀ v ∈ typeSpace D, ∀ i, 0 ≤ M.utility i (v i) v
  alloc_measurable : ∀ i, MeasurableSet {v | i ∈ M.alloc v}
  pay_measurable : ∀ i, Measurable (fun v => M.pay v i)
  pay_integrable : ∀ i, Integrable (fun v => M.pay v i) (prior D)

/-- The expected revenue `𝔼_v[∑ᵢ πᵢ(v)]` of a mechanism under the prior. -/
noncomputable def revenue (D : ι → ValueDist) (M : Mechanism ι) : ℝ :=
  ∫ v, ∑ i, M.pay v i ∂(prior D)

/-- Definition 1 (p. 12): the virtual surplus `Φ(S, v) = ∑_{i ∈ S} φᵢ(vᵢ)` of a set `S`. -/
noncomputable def virtualSurplus (D : ι → ValueDist) (S : Finset ι) (v : ι → ℝ) : ℝ :=
  ∑ i ∈ S, (D i).virtualValue (v i)

end CHMSPricing.OpmUniform
