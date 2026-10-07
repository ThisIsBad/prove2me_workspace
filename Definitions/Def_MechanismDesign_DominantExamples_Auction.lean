import Mathlib

namespace MechanismDesign.DominantExamples

/-- The single unit auction environment of Börgers, *An Introduction to the Theory of Mechanism
Design*, §4.2.1 (pp.78–79): every buyer's type lies in the common interval `[θ̲, θ̄]` with
`0 ≤ θ̲ < θ̄`. No prior over types is assumed in Chapter 4. -/
structure AuctionSetting where
  /-- lower end `θ̲` of the type interval -/
  lo : ℝ
  /-- upper end `θ̄` of the type interval -/
  hi : ℝ
  lo_nonneg : 0 ≤ lo
  lo_lt_hi : lo < hi

namespace AuctionSetting

/-- The set of type vectors `Θ = [θ̲, θ̄]^I`. -/
def typeSpace (E : AuctionSetting) (ι : Type*) : Set (ι → ℝ) :=
  Set.univ.pi fun _ => Set.Icc E.lo E.hi

end AuctionSetting

/-- A direct mechanism for the single unit auction (Definition 3.1, p.34, used in §4.2.2):
an allocation rule `q : Θ → Δ`, where `Δ` is the set of vectors `(q_1, …, q_N)` with
`0 ≤ q_i ≤ 1` and `∑_i q_i ≤ 1` (`q i θ` is the probability that buyer `i` obtains the good),
and payment rules `t_i : Θ → ℝ` (`t i θ` is buyer `i`'s transfer to the seller). The
constraints are imposed on `Θ` only; values outside `Θ` play no role. -/
structure AuctionMechanism (E : AuctionSetting) (ι : Type*) [Fintype ι] where
  /-- allocation rule: `q i θ` is the probability that buyer `i` gets the good -/
  q : ι → (ι → ℝ) → ℝ
  /-- payment rule: `t i θ` is the payment of buyer `i` -/
  t : ι → (ι → ℝ) → ℝ
  q_nonneg : ∀ θ ∈ E.typeSpace ι, ∀ i, 0 ≤ q i θ
  q_le_one : ∀ θ ∈ E.typeSpace ι, ∀ i, q i θ ≤ 1
  sum_q_le_one : ∀ θ ∈ E.typeSpace ι, ∑ i, q i θ ≤ 1

namespace AuctionMechanism

variable {E : AuctionSetting} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Buyer `i`'s ex post utility under truthful reporting at the type vector `θ`:
`u_i(θ) = θ_i q_i(θ) − t_i(θ)`. -/
def u (M : AuctionMechanism E ι) (i : ι) (θ : ι → ℝ) : ℝ :=
  θ i * M.q i θ - M.t i θ

/-- Definition 4.1 (p.80), dominant strategy incentive compatibility: for all `i`, all
`θ_i, θ_i' ∈ [θ̲, θ̄]` and all `θ_{-i} ∈ Θ_{-i}`,
`θ_i q_i(θ_i, θ_{-i}) − t_i(θ_i, θ_{-i}) ≥ θ_i q_i(θ_i', θ_{-i}) − t_i(θ_i', θ_{-i})`.
The pair `(θ_i, θ_{-i})` is the type vector `θ ∈ Θ`; `(θ_i', θ_{-i})` is
`Function.update θ i x`. -/
def IsDSIC (M : AuctionMechanism E ι) : Prop :=
  ∀ i, ∀ θ ∈ E.typeSpace ι, ∀ x ∈ Set.Icc E.lo E.hi,
    θ i * M.q i (Function.update θ i x) - M.t i (Function.update θ i x) ≤
      θ i * M.q i θ - M.t i θ

/-- Definition 4.2 (p.80), ex post individual rationality: for all `i` and all `θ ∈ Θ`,
`θ_i q_i(θ) − t_i(θ) ≥ 0`. -/
def IsEPIR (M : AuctionMechanism E ι) : Prop :=
  ∀ i, ∀ θ ∈ E.typeSpace ι, 0 ≤ θ i * M.q i θ - M.t i θ

end AuctionMechanism

open Classical in
/-- The number `n` of agents `k` with `ψ_k(θ_k) = ψ_i(θ_i)` (Definition 4.3, p.82); it counts
`i` itself, so it is at least `1`. -/
noncomputable def tieCount {ι : Type*} [Fintype ι] (ψ : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι) : ℕ :=
  (Finset.univ.filter fun k => ψ k (θ k) = ψ i (θ i)).card

open Classical in
/-- The allocation rule of a canonical auction (Definition 4.3, p.82):
`q_i(θ) = 1/n` if `ψ_i(θ_i) ≥ 0` and `ψ_i(θ_i) ≥ ψ_j(θ_j)` for all `j ≠ i`, where `n` is the
number of agents `k` with `ψ_k(θ_k) = ψ_i(θ_i)`; `q_i(θ) = 0` otherwise. -/
noncomputable def canonicalAuctionQ {ι : Type*} [Fintype ι] (ψ : ι → ℝ → ℝ) (i : ι)
    (θ : ι → ℝ) : ℝ :=
  if 0 ≤ ψ i (θ i) ∧ ∀ j, j ≠ i → ψ j (θ j) ≤ ψ i (θ i) then
    1 / (tieCount ψ θ i : ℝ)
  else 0

open Classical in
/-- The payment rule of a canonical auction (Definition 4.3, p.82):
`t_i(θ) = (1/n) · min {θ̂_i ∈ [θ̲, θ̄] | q_i(θ̂_i, θ_{-i}) > 0}` if `q_i(θ) > 0`, and
`t_i(θ) = 0` if `q_i(θ) = 0`. The minimum is written as `sInf`; when `q_i(θ) > 0` the set
contains `θ_i` and, for continuous strictly increasing `ψ_i`, is a closed subinterval of
`[θ̲, θ̄]`, so the infimum is attained. -/
noncomputable def canonicalAuctionT {ι : Type*} [Fintype ι] [DecidableEq ι] (E : AuctionSetting)
    (ψ : ι → ℝ → ℝ) (i : ι) (θ : ι → ℝ) : ℝ :=
  if 0 < canonicalAuctionQ ψ i θ then
    (1 / (tieCount ψ θ i : ℝ)) *
      sInf {x | x ∈ Set.Icc E.lo E.hi ∧ 0 < canonicalAuctionQ ψ i (Function.update θ i x)}
  else 0

/-- Definition 4.3 (p.82), canonical auction: there are strictly increasing and continuous
functions `ψ_i : [θ̲, θ̄] → ℝ` such that for all `θ ∈ Θ` and all `i` the allocation and the
payment of the mechanism are `canonicalAuctionQ ψ i θ` and `canonicalAuctionT E ψ i θ`. -/
def AuctionMechanism.IsCanonical {E : AuctionSetting} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : AuctionMechanism E ι) : Prop :=
  ∃ ψ : ι → ℝ → ℝ,
    (∀ i, StrictMonoOn (ψ i) (Set.Icc E.lo E.hi) ∧ ContinuousOn (ψ i) (Set.Icc E.lo E.hi)) ∧
    ∀ θ ∈ E.typeSpace ι, ∀ i,
      M.q i θ = canonicalAuctionQ ψ i θ ∧ M.t i θ = canonicalAuctionT E ψ i θ

end MechanismDesign.DominantExamples
