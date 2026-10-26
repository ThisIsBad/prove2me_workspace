import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_RegretBandits_Stochastic_model

namespace RegretBandits.Stochastic

open ImprovedLinBandits.UCBDelta

/-- The (α, ψ)-UCB index of arm `j` used to choose the arm of round `t + 1`
(Bubeck and Cesa-Bianchi, arXiv:1204.5721v2, p. 10):
`μ̂_{j, T_j(t)} + (ψ*)⁻¹(α ln(t + 1) / T_j(t))`, where `T_j(t) = pullCount I j t ω` is the number
of times arm `j` was played in rounds `1, …, t`. Only used when `T_j(t) ≥ 1`. -/
noncomputable def ucbIndex {Ω : Type*} {K : ℕ} (ψ : ℝ → ℝ) (α : ℝ) (X : Fin K → ℕ → Ω → ℝ)
    (I : ℕ → Ω → Fin K) (j : Fin K) (t : ℕ) (ω : Ω) : ℝ :=
  sampleMean X j (pullCount I j t ω) ω +
    lfInv ψ (α * Real.log ((t : ℝ) + 1) / (pullCount I j t ω : ℝ))

/-- `I` is a run of (α, ψ)-UCB (p. 10) on the reward stack `X`: for every outcome `ω` and every
round `t + 1`,
1. if some arm has not been played in rounds `1, …, t` (its index `α ln t / 0` is `+∞`), then
   `I (t + 1) ω` is such an unplayed arm; in particular rounds `1, …, K` play every arm once;
2. otherwise `I (t + 1) ω` maximizes the index `ucbIndex` over all arms.
Every tie-breaking rule is allowed. -/
def IsAlphaPsiUCBRun {Ω : Type*} {K : ℕ} (ψ : ℝ → ℝ) (α : ℝ) (X : Fin K → ℕ → Ω → ℝ)
    (I : ℕ → Ω → Fin K) : Prop :=
  ∀ (ω : Ω) (t : ℕ),
    ((∃ j : Fin K, pullCount I j t ω = 0) → pullCount I (I (t + 1) ω) t ω = 0) ∧
    ((∀ j : Fin K, pullCount I j t ω ≠ 0) → ∀ j : Fin K,
      ucbIndex ψ α X I j t ω ≤ ucbIndex ψ α X I (I (t + 1) ω) t ω)

end RegretBandits.Stochastic
