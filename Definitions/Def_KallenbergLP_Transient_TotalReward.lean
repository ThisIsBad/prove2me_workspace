import Definitions.Def_KallenbergLP_Transient_Policy
set_option autoImplicit false

namespace KallenbergLP.Transient

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- The expected reward `v^{t+1}_i(R)` in period `t + 1` (Lean index `t`), p. 22. -/
def periodReward (M : MDP N α) (r : Fin N → α → ℝ) (R : Policy M)
    (i : Fin N) (t : ℕ) : ℝ :=
  ∑ j : Fin N, ∑ a ∈ M.actions j, occupancy M R i j a t * r j a

/-- Expected reward over the first `T` epochs, using the occupancies of §2.2. -/
def cumulativeReward (M : MDP N α) (r : Fin N → α → ℝ) (R : Policy M)
    (i : Fin N) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, periodReward M r R i t

/-- Assumption 3.2.1: every policy has an extended-real total reward limit. -/
def TotalRewardExists (M : MDP N α) (r : Fin N → α → ℝ) : Prop :=
  ∀ (R : Policy M) (i : Fin N),
    ∃ v : EReal,
      Filter.Tendsto (fun T : ℕ => (cumulativeReward M r R i T : EReal))
        Filter.atTop (nhds v)

/-- The extended-real total reward `v_i(R)` of one policy (the limit, under Assumption 3.2.1). -/
noncomputable def policyValue (M : MDP N α) (r : Fin N → α → ℝ) (R : Policy M)
    (i : Fin N) : EReal :=
  Filter.limsup (fun T : ℕ => (cumulativeReward M r R i T : EReal)) Filter.atTop

/-- The TMD value vector takes the supremum over every history-dependent randomized policy. -/
noncomputable def valueVector (M : MDP N α) (r : Fin N → α → ℝ) (i : Fin N) : EReal :=
  ⨆ R : Policy M, policyValue M r R i

/-- The expected discounted reward `v^δ_i(R) = ∑_{t ≥ 1} δ^{t-1} v^t_i(R)`, p. 22
(Lean index `t` is epoch `t + 1`). -/
noncomputable def discountedValue (M : MDP N α) (r : Fin N → α → ℝ) (R : Policy M)
    (i : Fin N) (δ : ℝ) : ℝ :=
  ∑' t : ℕ, δ ^ t * periodReward M r R i t

/-- Definition 3.2.1: an extended-real vector `x` is p-summable if no sum `∑_j p_iaj x_j`
with `a ∈ A(i)` contains both a `+∞` and a `−∞` term (terms with `p_iaj = 0` are `0`). -/
def PSummable (M : MDP N α) (x : Fin N → EReal) : Prop :=
  ∀ i a, a ∈ M.actions i →
    ¬ ((∃ j, 0 < M.transition i a j ∧ x j = ⊤) ∧
       (∃ k, 0 < M.transition i a k ∧ x k = ⊥))

/-- The right-hand side `max_{a ∈ A(i)} {r_ia + ∑_j p_iaj x_j}` of the functional equation
of Theorem 3.2.2, computed in `EReal`. -/
noncomputable def bellmanRHS (M : MDP N α) (r : Fin N → α → ℝ) (x : Fin N → EReal)
    (i : Fin N) : EReal :=
  (M.actions i).sup' (M.actions_nonempty i) fun a =>
    (r i a : EReal) + ∑ j : Fin N, (M.transition i a j : EReal) * x j

end KallenbergLP.Transient
