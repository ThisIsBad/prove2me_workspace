import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction

namespace PolicyGradTheory.ProjGA

open FoundationsML.ReinforcementLearning

/-- A probability distribution on a finite type: nonnegative weights summing to one
(the start distributions `ρ, µ ∈ ∆(S)` of arXiv:1908.00261v5, §3, p. 9). -/
def IsDist {X : Type*} [Fintype X] (μ : X → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

/-- The standing setting of §3 (p. 9): a finite MDP with transition kernel `P`
(`P s a s'` = P(s'|s,a)), rewards `r(s,a) ∈ [0,1]` and discount factor `γ ∈ [0,1)`. -/
def IsFiniteMDP {S A : Type*} [Fintype S] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) : Prop :=
  IsTransitionKernel P ∧ (∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) ∧ 0 ≤ γ ∧ γ < 1

/-- `V^π(ρ) = E_{s₀∼ρ}[V^π(s₀)]` (p. 10). -/
noncomputable def valueAt {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (ρ : S → ℝ) : ℝ :=
  ∑ s, ρ s * PolicyValue π P r γ s

/-- The advantage `A^π(s,a) = Q^π(s,a) − V^π(s)` (p. 10). -/
noncomputable def advantage {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (s : S) (a : A) : ℝ :=
  QFunction π P r γ s a - PolicyValue π P r γ s

/-- The discounted state visitation distribution (4) (p. 11):
`d^π_ρ(s) = E_{s₀∼ρ}[(1−γ) ∑_{t≥0} γ^t Pr^π(s_t = s | s₀)]`. -/
noncomputable def visitation {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ) (s : S) : ℝ :=
  (1 - γ) * ∑' t : ℕ, γ ^ t * ∑ s₀, ρ s₀ * OccupationDist π P s₀ t s

end PolicyGradTheory.ProjGA
