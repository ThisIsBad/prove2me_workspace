import Mathlib

namespace FoundationsRL.Structured

/-- Regret for the structured bandit protocol (Foster & Rakhlin, *Foundations of Reinforcement
Learning and Interactive Decision Making*, arXiv:2312.16730v1, Eq. (4.3), p. 57):

`Reg := ∑_{t=1}^T f⋆(π⋆) − ∑_{t=1}^T E_{π_t ∼ p_t}[f⋆(π_t)]`,

the cumulative gap between the optimal decision's reward and the expected reward of the
decision-maker's realized action distributions `p : Fin T → S → ℝ` (`p t` a probability vector
over the decision space `Π`) under the ground-truth mean reward function `fstar` and optimal
decision `piStar`. -/
noncomputable def regret {S : Type*} [Fintype S] (fstar : S → ℝ) (piStar : S) (T : ℕ)
    (p : Fin T → S → ℝ) : ℝ :=
  ∑ t : Fin T, (fstar piStar - ∑ π : S, p t π * fstar π)

end FoundationsRL.Structured
