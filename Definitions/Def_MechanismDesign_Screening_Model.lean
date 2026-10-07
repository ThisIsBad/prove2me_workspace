import Mathlib

/-!
# Screening a single indivisible good (Börgers, Ch. 2, §2.2, pp.6–11)

One seller, one buyer, one indivisible good. The buyer's type `θ` is distributed on the interval
`[θ̲, θ̄]` (`θlo`, `θhi`) with `0 ≤ θ̲ < θ̄`, cumulative distribution function `F` and a density
`f` that is strictly positive on the interval (p.7).

Functions of the type are total functions `ℝ → ℝ`; only their values on `[θ̲, θ̄]` matter, and
every condition below quantifies over `θ ∈ [θ̲, θ̄]` only.
-/

namespace MechanismDesign.Screening

open MeasureTheory

/-- The seller's belief about the buyer's type (p.7): a density `f`, strictly positive on
`[θ̲, θ̄]`, integrable there with total mass `1`, and its cumulative distribution function
`F(θ) = ∫_{θ̲}^{θ} f(x) dx` on `[θ̲, θ̄]`. The support is `[θ̲, θ̄]` with `0 ≤ θ̲ < θ̄`. -/
structure TypeDistribution (θlo θhi : ℝ) where
  /-- The density `f`. -/
  f : ℝ → ℝ
  /-- The cumulative distribution function `F`. -/
  F : ℝ → ℝ
  /-- `0 ≤ θ̲`. -/
  lo_nonneg : 0 ≤ θlo
  /-- `θ̲ < θ̄`. -/
  lo_lt_hi : θlo < θhi
  /-- `f(θ) > 0` for all `θ ∈ [θ̲, θ̄]`. -/
  f_pos : ∀ θ ∈ Set.Icc θlo θhi, 0 < f θ
  /-- `f` is integrable on `[θ̲, θ̄]`. -/
  f_integrable : IntervalIntegrable f volume θlo θhi
  /-- `f` is a probability density on `[θ̲, θ̄]`. -/
  f_total : ∫ x in θlo..θhi, f x = 1
  /-- `F(θ) = ∫_{θ̲}^{θ} f(x) dx` for `θ ∈ [θ̲, θ̄]`. -/
  F_eq : ∀ θ ∈ Set.Icc θlo θhi, F θ = ∫ x in θlo..θ, f x

/-- A **direct mechanism** (Definition 2.1, p.9): a probability of transferring the good
`q : [θ̲, θ̄] → [0, 1]` and a payment `t : [θ̲, θ̄] → ℝ`, as functions of the reported type. -/
structure DirectMechanism (θlo θhi : ℝ) where
  /-- Probability `q(θ)` that the buyer who reports `θ` obtains the good. -/
  q : ℝ → ℝ
  /-- Payment `t(θ)` of the buyer who reports `θ`. -/
  t : ℝ → ℝ
  /-- `q(θ) ∈ [0, 1]` for all `θ ∈ [θ̲, θ̄]`. -/
  q_mem : ∀ θ ∈ Set.Icc θlo θhi, q θ ∈ Set.Icc (0 : ℝ) 1

variable {θlo θhi : ℝ}

/-- The buyer's expected utility `u(θ) = θ q(θ) − t(θ)` when his type is `θ` and he reports
truthfully (p.10). -/
def DirectMechanism.u (m : DirectMechanism θlo θhi) (θ : ℝ) : ℝ :=
  θ * m.q θ - m.t θ

/-- **Incentive compatibility** (Definition 2.2, p.10): `u(θ) ≥ θ q(θ′) − t(θ′)` for all
`θ, θ′ ∈ [θ̲, θ̄]`. -/
def DirectMechanism.IsIC (m : DirectMechanism θlo θhi) : Prop :=
  ∀ θ ∈ Set.Icc θlo θhi, ∀ θ' ∈ Set.Icc θlo θhi, θ * m.q θ' - m.t θ' ≤ m.u θ

/-- **Individual rationality** (Definition 2.3, p.11): `u(θ) ≥ 0` for all `θ ∈ [θ̲, θ̄]`. -/
def DirectMechanism.IsIR (m : DirectMechanism θlo θhi) : Prop :=
  ∀ θ ∈ Set.Icc θlo θhi, 0 ≤ m.u θ

/-- The seller's expected revenue `∫_{θ̲}^{θ̄} t(θ) f(θ) dθ` (pp.6, 15). -/
noncomputable def expectedRevenue (D : TypeDistribution θlo θhi) (m : DirectMechanism θlo θhi) :
    ℝ :=
  ∫ θ in θlo..θhi, m.t θ * D.f θ

/-- The posted-price mechanism at price `p` (Proposition 2.5, p.17): the buyer obtains the good
and pays `p` if `θ ≥ p`, and obtains nothing and pays nothing if `θ < p`. (At the tie `θ = p` the
book leaves the value open; this definition fixes `q(p) = 1`, `t(p) = p`.) -/
noncomputable def postedPrice (θlo θhi p : ℝ) : DirectMechanism θlo θhi where
  q θ := if p ≤ θ then 1 else 0
  t θ := if p ≤ θ then p else 0
  q_mem θ _ := by
    by_cases h : p ≤ θ <;> simp [h]

/-- A general (indirect) selling mechanism, in reduced form (pp.8–10). The seller commits to an
extensive game and to her own strategy in it; what remains is the buyer's choice among his
strategies `s ∈ S`, each of which results in a probability `prob s ∈ [0, 1]` of obtaining the good
and an expected payment `pay s`. The buyer is risk neutral with quasi-linear utility, so these two
numbers are all that his expected utility depends on. `S` is an arbitrary type. -/
structure Mechanism where
  /-- The buyer's strategies in the game. -/
  S : Type
  /-- Probability of purchase resulting from strategy `s`. -/
  prob : S → ℝ
  /-- Expected payment resulting from strategy `s`. -/
  pay : S → ℝ
  /-- Purchase probabilities lie in `[0, 1]`. -/
  prob_mem : ∀ s, prob s ∈ Set.Icc (0 : ℝ) 1

/-- `σ` is an **optimal buyer strategy** in the mechanism `Γ` (p.10): for every type
`θ ∈ [θ̲, θ̄]`, the strategy `σ(θ)` maximizes the buyer's expected utility `θ · prob − pay`
among all his strategies. -/
def Mechanism.IsOptimalStrategy (θlo θhi : ℝ) (Γ : Mechanism) (σ : ℝ → Γ.S) : Prop :=
  ∀ θ ∈ Set.Icc θlo θhi, ∀ s : Γ.S,
    θ * Γ.prob s - Γ.pay s ≤ θ * Γ.prob (σ θ) - Γ.pay (σ θ)

/-- `σ : [θ̲, θ̄] → [θ̲, θ̄]` is an **optimal buyer strategy in the direct mechanism** `m`
(pp.9–10): it maps types to reports in `[θ̲, θ̄]`, and for every type `θ` the report `σ(θ)`
maximizes `θ q(θ′) − t(θ′)` over all reports `θ′ ∈ [θ̲, θ̄]`. -/
def DirectMechanism.IsOptimalStrategy (m : DirectMechanism θlo θhi) (σ : ℝ → ℝ) : Prop :=
  ∀ θ ∈ Set.Icc θlo θhi, σ θ ∈ Set.Icc θlo θhi ∧
    ∀ θ' ∈ Set.Icc θlo θhi, θ * m.q θ' - m.t θ' ≤ θ * m.q (σ θ) - m.t (σ θ)

end MechanismDesign.Screening
