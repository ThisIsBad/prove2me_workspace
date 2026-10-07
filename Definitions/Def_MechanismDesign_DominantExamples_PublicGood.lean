import Mathlib

namespace MechanismDesign.DominantExamples

/-- The public goods environment of Börgers, *An Introduction to the Theory of Mechanism
Design*, §4.3.1 (pp.84–85): agents decide whether to produce an indivisible nonexcludable public
good at cost `c > 0`; every agent's type lies in `[θ̲, θ̄]` with `0 ≤ θ̲ < θ̄`, and agent `i`'s
utility from decision `g ∈ {0, 1}` and transfer `t_i` is `θ_i g − t_i`. No prior is assumed. -/
structure PublicGoodSetting where
  /-- lower end `θ̲` of the type interval -/
  lo : ℝ
  /-- upper end `θ̄` of the type interval -/
  hi : ℝ
  /-- cost `c` of producing the public good -/
  c : ℝ
  lo_nonneg : 0 ≤ lo
  lo_lt_hi : lo < hi
  c_pos : 0 < c

namespace PublicGoodSetting

/-- The set of type vectors `Θ = [θ̲, θ̄]^I`. -/
def typeSpace (E : PublicGoodSetting) (ι : Type*) : Set (ι → ℝ) :=
  Set.univ.pi fun _ => Set.Icc E.lo E.hi

end PublicGoodSetting

/-- A deterministic direct mechanism for the public good (Definition 3.4, p.47, used in
§4.3.2): a decision rule `q : Θ → {0, 1}` and transfer rules `t_i : Θ → ℝ` (`t i θ` is the
transfer agent `i` makes to the community). The decision rule takes values in `{0, 1}` on
`Θ`; values outside `Θ` play no role. -/
structure PublicGoodMechanism (E : PublicGoodSetting) (ι : Type*) where
  /-- decision rule: `q θ = 1` if the good is produced, `0` otherwise -/
  q : (ι → ℝ) → ℝ
  /-- transfer rule: `t i θ` is agent `i`'s transfer -/
  t : ι → (ι → ℝ) → ℝ
  q_mem : ∀ θ ∈ E.typeSpace ι, q θ = 0 ∨ q θ = 1

namespace PublicGoodMechanism

variable {E : PublicGoodSetting} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Agent `i`'s ex post utility under truthful reporting: `u_i(θ) = θ_i q(θ) − t_i(θ)`. -/
def u (M : PublicGoodMechanism E ι) (i : ι) (θ : ι → ℝ) : ℝ :=
  θ i * M.q θ - M.t i θ

/-- Dominant strategy incentive compatibility (§4.3.2, "as in the auction example",
Definition 4.1): for all `i`, all `θ ∈ Θ` and all reports `θ_i' ∈ [θ̲, θ̄]`,
`θ_i q(θ_i', θ_{-i}) − t_i(θ_i', θ_{-i}) ≤ θ_i q(θ) − t_i(θ)`. -/
def IsDSIC (M : PublicGoodMechanism E ι) : Prop :=
  ∀ i, ∀ θ ∈ E.typeSpace ι, ∀ x ∈ Set.Icc E.lo E.hi,
    θ i * M.q (Function.update θ i x) - M.t i (Function.update θ i x) ≤
      θ i * M.q θ - M.t i θ

/-- Ex post individual rationality (§4.3.2, Definition 4.2): `θ_i q(θ) − t_i(θ) ≥ 0` for all
`i` and all `θ ∈ Θ`. -/
def IsEPIR (M : PublicGoodMechanism E ι) : Prop :=
  ∀ i, ∀ θ ∈ E.typeSpace ι, 0 ≤ θ i * M.q θ - M.t i θ

/-- Ex post budget balance, written as an equality as in §4.3.2 (p.85):
`∑_i t_i(θ) = c q(θ)` for all `θ ∈ Θ`. -/
def IsBudgetBalanced (M : PublicGoodMechanism E ι) : Prop :=
  ∀ θ ∈ E.typeSpace ι, ∑ i, M.t i θ = E.c * M.q θ

end PublicGoodMechanism

open Classical in
/-- The decision rule of a canonical public good mechanism (Definition 4.4, p.87):
`q(θ) = 1` if `∑_i ψ_i(θ_i) ≥ c`, and `q(θ) = 0` otherwise. -/
noncomputable def canonicalPGQ {ι : Type*} [Fintype ι] (E : PublicGoodSetting)
    (ψ : ι → ℝ → ℝ) (θ : ι → ℝ) : ℝ :=
  if E.c ≤ ∑ i, ψ i (θ i) then 1 else 0

open Classical in
/-- The transfer rule of a canonical public good mechanism (Definition 4.4, p.87):
`t_i(θ) = min {θ̂_i ∈ [θ̲, θ̄] | ψ_i(θ̂_i) + ∑_{j ≠ i} ψ_j(θ_j) ≥ c}` if `q(θ) = 1`, and
`t_i(θ) = 0` if `q(θ) = 0`. The minimum is written as `sInf`; when `q(θ) = 1` the set contains
`θ_i` and, for continuous `ψ_i`, is closed, so the infimum is attained. -/
noncomputable def canonicalPGT {ι : Type*} [Fintype ι] [DecidableEq ι] (E : PublicGoodSetting)
    (ψ : ι → ℝ → ℝ) (i : ι) (θ : ι → ℝ) : ℝ :=
  if canonicalPGQ E ψ θ = 1 then
    sInf {x | x ∈ Set.Icc E.lo E.hi ∧ E.c ≤ ψ i x + ∑ j ∈ Finset.univ.erase i, ψ j (θ j)}
  else 0

/-- Definition 4.4 (p.87), canonical public good mechanism: for every agent `i` there is a
strictly increasing and continuous function `ψ_i : [θ̲, θ̄] → ℝ` such that for all `θ ∈ Θ` the
decision is `canonicalPGQ E ψ θ` and every transfer is `canonicalPGT E ψ i θ`. -/
def PublicGoodMechanism.IsCanonical {E : PublicGoodSetting} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : PublicGoodMechanism E ι) : Prop :=
  ∃ ψ : ι → ℝ → ℝ,
    (∀ i, StrictMonoOn (ψ i) (Set.Icc E.lo E.hi) ∧ ContinuousOn (ψ i) (Set.Icc E.lo E.hi)) ∧
    ∀ θ ∈ E.typeSpace ι,
      M.q θ = canonicalPGQ E ψ θ ∧ ∀ i, M.t i θ = canonicalPGT E ψ i θ

end MechanismDesign.DominantExamples
