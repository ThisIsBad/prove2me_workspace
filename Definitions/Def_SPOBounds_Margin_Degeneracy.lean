import Mathlib
import Definitions.Def_SPOBounds_Margin_Model

namespace SPOBounds.Margin

/-- The set of degenerate cost vector predictions (Definition 2, p. 13):
`𝒞° = {ĉ : P(ĉ) has multiple optimal solutions}`, i.e. `v ↦ ĉ v` has two distinct minimizers
over `S`. -/
def degenerate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) : Set (StrongDual ℝ E) :=
  {chat | ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ IsMinOn (fun x => chat x) S u ∧
    IsMinOn (fun x => chat x) S v}

/-- The distance to degeneracy `ν_S(ĉ) = inf_{c ∈ 𝒞°} ‖c − ĉ‖_*` (Definition 2, p. 13),
measured in the operator (= dual) norm. When `S` has two distinct points, `0 ∈ 𝒞°`, so the
infimum is over a nonempty set. -/
noncomputable def nu {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (chat : StrongDual ℝ E) : ℝ :=
  Metric.infDist chat (degenerate S)

/-- The strength property (Definition 3, p. 14), for the oracle `w` and parameter `μ`:
`ĉᵀ(v − w*(ĉ)) ≥ (μ ν_S(ĉ) / 2) ‖v − w*(ĉ)‖²` for all `v ∈ S` and all `ĉ`.
The requirement `μ > 0` is carried separately by every theorem. -/
def StrengthProperty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (μ : ℝ) (w : StrongDual ℝ E → E) : Prop :=
  ∀ chat : StrongDual ℝ E, ∀ v ∈ S,
    μ * nu S chat / 2 * ‖v - w chat‖ ^ 2 ≤ chat (v - w chat)

/-- The `γ`-margin SPO loss (Definition 4, p. 15; written `ℓ^γ_SPO` from p. 18 on):
`ℓ_SPO(ĉ, c)` if `ν_S(ĉ) > γ`, and
`(ν_S(ĉ)/γ) ℓ_SPO(ĉ, c) + (1 − ν_S(ĉ)/γ) ω_S(c)` if `ν_S(ĉ) ≤ γ`.
Every theorem using it assumes `γ > 0`. -/
noncomputable def marginLoss {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (w : StrongDual ℝ E → E) (γ : ℝ) (chat c : StrongDual ℝ E) : ℝ :=
  if γ < nu S chat then spoLoss w chat c
  else nu S chat / γ * spoLoss w chat c + (1 - nu S chat / γ) * omega S c

end SPOBounds.Margin
