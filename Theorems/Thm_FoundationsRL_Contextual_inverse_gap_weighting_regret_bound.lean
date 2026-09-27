import Mathlib
import Definitions.Def_FoundationsRL_Contextual_IsIGW


namespace FoundationsRL.Contextual

/-- Proposition 9 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, p. 49-50): the Inverse Gap Weighting
estimation-to-regret inequality. For any vector of estimated values `fhat : Fin A → ℝ`,
exploration parameter `γ > 0`, and distribution `p` satisfying `IsIGW A fhat γ bstar p`, the
inequality holds for every ground-truth vector `fstar : Fin A → ℝ` with optimal action
`pistar`. -/
theorem inverse_gap_weighting_regret_bound {A : ℕ} (fhat fstar : Fin A → ℝ) (γ : ℝ)
    (hγ : 0 < γ) (bstar : Fin A) (pistar : Fin A) (hpistar : ∀ π, fstar π ≤ fstar pistar)
    (p : Fin A → ℝ) (hp : IsIGW A fhat γ bstar p) :
    fstar pistar - ∑ π, p π * fstar π ≤ (A : ℝ) / γ + γ * ∑ π, p π * (fhat π - fstar π) ^ 2 := by sorry

end FoundationsRL.Contextual

