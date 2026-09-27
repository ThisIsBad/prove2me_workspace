import Mathlib

namespace FoundationsRL.Bandits

/-- The multi-armed bandit regret (Foster–Rakhlin, Eq. (2.3), p. 22),
`Reg := Σ_{t=1}^T f⋆(π⋆) − Σ_{t=1}^T E_{π_t ∼ p_t}[f⋆(π_t)]`,
for a mean reward function `fStar`, an optimal decision `piStar`, a horizon `T`,
and a sequence of per-round decision distributions `p : ℕ → Fin A → ℝ`
(`p t a` is the probability of playing `a` at round `t`; callers supply that
`p t` is a genuine probability vector when that fact is needed). -/
noncomputable def regret {A : ℕ} (fStar : Fin A → ℝ) (piStar : Fin A) (T : ℕ)
    (p : ℕ → Fin A → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, (fStar piStar - ∑ a : Fin A, p t a * fStar a)

end FoundationsRL.Bandits
