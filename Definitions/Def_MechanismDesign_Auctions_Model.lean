import Mathlib

open MeasureTheory

namespace MechanismDesign.Auctions

/-- The independent-private-values environment of Börgers §3.2.1 (p.32): buyers `ι` (at least
two), a common type interval `[lo, hi]` with `0 ≤ lo < hi`, and for every buyer `i` a density
`f i` of the valuation `θ_i`, strictly positive on `[lo, hi]` and integrating to `1` there.
Valuations are independent, so the joint density on `Θ = [lo, hi]^ι` is `∏ i, f i (θ i)`. -/
structure Environment (ι : Type*) [Fintype ι] where
  /-- the lower end `θ̲` of the common support -/
  lo : ℝ
  /-- the upper end `θ̄` of the common support -/
  hi : ℝ
  /-- the density `f_i` of buyer `i`'s valuation -/
  f : ι → ℝ → ℝ
  two_le_card : 2 ≤ Fintype.card ι
  lo_nonneg : 0 ≤ lo
  lo_lt_hi : lo < hi
  f_measurable : ∀ i, Measurable (f i)
  f_pos : ∀ i, ∀ x ∈ Set.Icc lo hi, 0 < f i x
  f_intervalIntegrable : ∀ i, IntervalIntegrable (f i) volume lo hi
  f_integral : ∀ i, ∫ x in lo..hi, f i x = 1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The type space `Θ = [θ̲, θ̄]^N`. -/
def Environment.typeSpace (E : Environment ι) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc E.lo E.hi)

/-- The common prior `F = ∏ F_i`: the law on `ι → ℝ` with density `θ ↦ ∏ i, f_i(θ_i)` on `Θ`
(and no mass outside `Θ`). -/
noncomputable def Environment.prior (E : Environment ι) : Measure (ι → ℝ) :=
  (volume.restrict E.typeSpace).withDensity (fun θ => ∏ i, ENNReal.ofReal (E.f i (θ i)))

/-- The cumulative distribution function `F_i(θ_i) = ∫_{θ̲}^{θ_i} f_i(x) dx`. -/
noncomputable def Environment.cdf (E : Environment ι) (i : ι) (x : ℝ) : ℝ :=
  ∫ y in E.lo..x, E.f i y

/-- The virtual valuation, Eq. (3.6): `ψ_i(θ_i) = θ_i − (1 − F_i(θ_i)) / f_i(θ_i)`. -/
noncomputable def Environment.virtualValue (E : Environment ι) (i : ι) (x : ℝ) : ℝ :=
  x - (1 - E.cdf i x) / E.f i x

/-- Regularity, Assumption 3.1 (p.41): every `ψ_i` is strictly increasing on `[θ̲, θ̄]`. -/
def Environment.Regular (E : Environment ι) : Prop :=
  ∀ i, StrictMonoOn (E.virtualValue i) (Set.Icc E.lo E.hi)

/-- A direct mechanism, Definition 3.1 (p.34): an allocation rule `q` with values in
`Δ = {(q_1,…,q_N) | 0 ≤ q_i ≤ 1, ∑ q_i ≤ 1}` on `Θ`, and payment rules `t_i : Θ → ℝ`.
Both are total functions on `ι → ℝ`; only their values on `Θ` matter. -/
structure DirectMechanism (E : Environment ι) where
  /-- `q i θ` is the probability that buyer `i` gets the good at the report profile `θ` -/
  q : ι → (ι → ℝ) → ℝ
  /-- `t i θ` is buyer `i`'s payment to the seller at the report profile `θ` -/
  t : ι → (ι → ℝ) → ℝ
  q_nonneg : ∀ θ ∈ E.typeSpace, ∀ i, 0 ≤ q i θ
  q_le_one : ∀ θ ∈ E.typeSpace, ∀ i, q i θ ≤ 1
  sum_q_le_one : ∀ θ ∈ E.typeSpace, ∑ i, q i θ ≤ 1

variable {E : Environment ι}

/-- The measurability and integrability the book leaves implicit (Ch. 2 note 2, p.235; Ch. 3
note 1): `q_i`, `t_i` are measurable, `t_i` is integrable under the prior, and so is every section
`θ_{-i} ↦ t_i(θ_i, θ_{-i})`, so that the interim payment `T_i(θ_i)` is a genuine expectation. -/
structure DirectMechanism.WellDefined (m : DirectMechanism E) : Prop where
  q_measurable : ∀ i, Measurable (m.q i)
  t_measurable : ∀ i, Measurable (m.t i)
  t_integrable : ∀ i, Integrable (m.t i) E.prior
  t_section_integrable : ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
    Integrable (fun θ => m.t i (Function.update θ i x)) E.prior

/-- Interim allocation probability, Eq. (3.1):
`Q_i(θ_i) = ∫_{Θ_{-i}} q_i(θ_i, θ_{-i}) f_{-i}(θ_{-i}) dθ_{-i}`, written as the prior expectation
of `q_i` with the `i`-th coordinate replaced by `θ_i`. -/
noncomputable def DirectMechanism.interimQ (m : DirectMechanism E) (i : ι) (x : ℝ) : ℝ :=
  ∫ θ, m.q i (Function.update θ i x) ∂E.prior

/-- Interim expected payment, Eq. (3.2). -/
noncomputable def DirectMechanism.interimT (m : DirectMechanism E) (i : ι) (x : ℝ) : ℝ :=
  ∫ θ, m.t i (Function.update θ i x) ∂E.prior

/-- Interim expected utility `U_i(θ_i) = θ_i Q_i(θ_i) − T_i(θ_i)` (p.36). -/
noncomputable def DirectMechanism.interimU (m : DirectMechanism E) (i : ι) (x : ℝ) : ℝ :=
  x * m.interimQ i x - m.interimT i x

/-- Bayesian incentive compatibility, Definition 3.2 (p.36). -/
def DirectMechanism.IsIC (m : DirectMechanism E) : Prop :=
  ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, ∀ x' ∈ Set.Icc E.lo E.hi,
    x * m.interimQ i x' - m.interimT i x' ≤ x * m.interimQ i x - m.interimT i x

/-- Interim individual rationality, Definition 3.3 (p.36). -/
def DirectMechanism.IsIR (m : DirectMechanism E) : Prop :=
  ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, 0 ≤ m.interimU i x

/-- The seller's expected revenue `E[∑_i t_i(θ)]`. -/
noncomputable def DirectMechanism.revenue (m : DirectMechanism E) : ℝ :=
  ∑ i, ∫ θ, m.t i θ ∂E.prior

/-- Expected utilitarian welfare `E[∑_i q_i(θ) θ_i]`, Eq. (3.8) (p.42). -/
noncomputable def DirectMechanism.welfare (m : DirectMechanism E) : ℝ :=
  ∫ θ, ∑ i, m.q i θ * θ i ∂E.prior

/-- The comparison class of §3.2.4–3.2.5: well-defined, incentive-compatible and individually
rational direct mechanisms. -/
def DirectMechanism.Admissible (m : DirectMechanism E) : Prop :=
  m.WellDefined ∧ m.IsIC ∧ m.IsIR

/-- Myerson's allocation rule, Eq. (3.7) / Proposition 3.4 (i): the good goes to `i` iff
`ψ_i(θ_i) > 0` and `ψ_i(θ_i) > ψ_j(θ_j)` for every `j ≠ i`; otherwise `q_i(θ) = 0`. -/
noncomputable def Environment.myersonAlloc (E : Environment ι) (i : ι) (θ : ι → ℝ) : ℝ := by
  classical
  exact if 0 < E.virtualValue i (θ i) ∧ ∀ j, j ≠ i → E.virtualValue j (θ j) < E.virtualValue i (θ i)
    then 1 else 0

/-- The efficient allocation rule, Proposition 3.5 (i): the good goes to `i` iff `θ_i > θ_j`
for every `j ≠ i`; otherwise `q_i(θ) = 0`. -/
noncomputable def efficientAlloc (i : ι) (θ : ι → ℝ) : ℝ := by
  classical
  exact if ∀ j, j ≠ i → θ j < θ i then 1 else 0

end MechanismDesign.Auctions
