import Mathlib

namespace FoundationsRL.Contextual

/-- Regret against the best-in-hindsight context-dependent policy, as defined for the
contextual bandit protocol (Foster & Rakhlin, *Foundations of Reinforcement Learning and
Interactive Decision Making*, arXiv:2312.16730v1, Eq. (3.3), p. 39):

`Reg := ∑_{t=1}^T fstar(x_t, pistar(x_t)) - ∑_{t=1}^T E_{π_t ∼ p_t}[fstar(x_t, π_t)]`,

the cumulative gap between the optimal policy's reward and the expected reward of the
decision-maker's realized action distributions `p : Fin T → Fin A → ℝ` (`p t` a probability
vector over `Fin A`) under context sequence `x` and ground-truth reward function `fstar`. -/
def regret {X : Type*} (A T : ℕ) (x : Fin T → X) (fstar : X → Fin A → ℝ) (pistar : X → Fin A)
    (p : Fin T → Fin A → ℝ) : ℝ :=
  ∑ t : Fin T, (fstar (x t) (pistar (x t)) - ∑ a : Fin A, p t a * fstar (x t) a)

end FoundationsRL.Contextual
