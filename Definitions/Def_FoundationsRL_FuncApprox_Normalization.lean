import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI

/-!
The standing reward normalization of Foster & Rakhlin, *Foundations of Reinforcement Learning
and Interactive Decision Making* (arXiv:2312.16730v1), Section 7 (function approximation):
"we will assume that `Σ_{h=1}^H r_h ∈ [0,1]` unless otherwise specified" (p. 129) and "assume
that both cumulative and individual-step rewards are in `[0,1]`" (p. 132), together with the
convention, used throughout §7, that a value-function class `𝒬` consists of `[0,1]`-valued
functions (p. 132: "for `Q : S × A → [0,1]`"; the class is assumed to contain `Q^{M,⋆}`, which
is `[0,1]`-valued under the normalization). These are the hypotheses that make Hoeffding's
inequality (Lemma 29) and the Bellman-rank analysis of BiLinUCB (Lemma 30, Proposition 47)
valid; the retired statements omitted them.

In the platform's `EpisodicMDP` the reward of a step is recorded through its mean `M.R h s a`
and, as in `FuncApprox.BiLinUCB`, every realized reward is identified with that mean (the
MDP has deterministic rewards). The almost-sure cumulative bound `Σ_h r_h ∈ [0,1]` therefore
becomes: along every trajectory of positive probability (positive initial mass and positive
transition probabilities at every layer, hence reachable under some policy), the sum of the
layer rewards is at most `1`; the lower bound `0` follows from the per-step bound. -/

namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

/-- `τ` is a trajectory of positive probability in `M`: its initial state has positive mass
under `d1` and every one of its `H` transitions has positive probability. These are exactly
the trajectories that occur with positive probability under some policy `π ∈ Π^{rns}` (e.g. the
uniform one), so an "almost sure" property of the trajectory under every policy is a property
of every such `τ`. -/
def ReachableTraj (M : EpisodicMDP S A H) (τ : Trajectory S A H) : Prop :=
  0 < M.d1 (stateAt τ 0) ∧
    ∀ h : Fin H, 0 < M.P h.1 (stateAt τ h.1) (actionAt τ h.1) (nextStateAt τ h.1)

/-- The Section 7 reward normalization (Foster–Rakhlin, p. 129 and p. 132): every per-step
mean reward lies in `[0,1]`, and the cumulative reward `Σ_{h=1}^H r_h` is at most `1` along
every trajectory of positive probability (the book's "`Σ_h r_h ∈ [0,1]` almost surely"). -/
def RewardsNormalized (M : EpisodicMDP S A H) : Prop :=
  (∀ h, h < H → ∀ s a, M.R h s a ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ τ : Trajectory S A H, ReachableTraj M τ →
      ∑ h ∈ Finset.range H, M.R h (stateAt τ h) (actionAt τ h) ≤ 1

end FoundationsRL.FuncApprox

namespace FoundationsRL.FuncApprox

/-- The value-function class realized by `qeval` (for horizon `H`) consists of `[0,1]`-valued
functions at every layer `h < H` (Foster–Rakhlin's standing convention for value-function
classes in Section 7, matching `Q^{M,⋆} ∈ [0,1]` under `RewardsNormalized`). -/
def IsNormalizedValueClass {S A Qc : Type*} (H : ℕ) (qeval : Qc → ℕ → S → A → ℝ) : Prop :=
  ∀ Qf : Qc, ∀ h, h < H → ∀ s a, qeval Qf h s a ∈ Set.Icc (0 : ℝ) 1

end FoundationsRL.FuncApprox
