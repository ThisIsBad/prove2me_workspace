import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_ValueDist
import Definitions.Def_CHMSPricing_UnitDemand_SetSystem

namespace CHMSPricing.UnitDemand

open MeasureTheory

/-- A deterministic direct mechanism for single-parameter agents `ι` (BSMD, §2.1, p. 4): it maps
a reported value profile `v` to an allocation `M(v)` (the set of served agents) and a payment
`πᵢ(v)` for each agent. -/
structure Mechanism (ι : Type*) where
  alloc : (ι → ℝ) → Finset ι
  pay : (ι → ℝ) → ι → ℝ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quasilinear utility of single-parameter agent `i` with true value `x` when the reported
profile is `b`. -/
noncomputable def Mechanism.utility (M : Mechanism ι) (i : ι) (x : ℝ) (b : ι → ℝ) : ℝ :=
  (if i ∈ M.alloc b then x else 0) - M.pay b i

/-- A truthful (dominant-strategy incentive compatible), ex-post individually rational
single-parameter mechanism respecting the feasibility constraint `J` on the type space, with
measurable allocation events and measurable, integrable payments (standing pin P3). -/
structure IsTruthful (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι) : Prop where
  feasible : ∀ v ∈ typeSpace D, J.Feasible (M.alloc v)
  dsic : ∀ v ∈ typeSpace D, ∀ i, ∀ x' ∈ Set.Icc (D i).lo (D i).hi,
    M.utility i (v i) (Function.update v i x') ≤ M.utility i (v i) v
  ir : ∀ v ∈ typeSpace D, ∀ i, 0 ≤ M.utility i (v i) v
  alloc_measurable : ∀ i, MeasurableSet {v | i ∈ M.alloc v}
  pay_measurable : ∀ i, Measurable (fun v => M.pay v i)
  pay_integrable : ∀ i, Integrable (fun v => M.pay v i) (prior D)

/-- The expected revenue `𝔼_v[∑ᵢ πᵢ(v)]` of a single-parameter mechanism under the prior. -/
noncomputable def revenue (D : ι → ValueDist) (M : Mechanism ι) : ℝ :=
  ∫ v, ∑ i, M.pay v i ∂(prior D)

/-- `q^M_i`: the probability over `v ∼ F` that `M` serves agent `i`. -/
noncomputable def servProb (D : ι → ValueDist) (M : Mechanism ι) (i : ι) : ℝ :=
  (prior D {v | i ∈ M.alloc v}).toReal

/-- `ℛ^obl_p` (§2.2, p. 4): the pessimistic expected revenue of the order-oblivious posted-price
mechanism with prices `p`, `𝔼_v [min_{S ∈ 𝒮_v} ∑_{i ∈ S} pᵢ]`, the minimum taken over the
(nonempty, finite) class of maximal feasible desiring sets. -/
noncomputable def oblRevenue (D : ι → ValueDist) (J : SetSystem ι) (p : ι → ℝ) : ℝ :=
  ∫ v, (maxFeasDesiringSets J p v).inf' (maxFeasDesiringSets_nonempty J p v)
    (fun S => ∑ i ∈ S, p i) ∂(prior D)

end CHMSPricing.UnitDemand
