import Mathlib

open scoped ENNReal NNReal
open Classical

namespace SennottDP.DiscountedASM

/-- A Markov decision chain (Sennott, §2.1, p. 16): for each state `i` a finite nonempty
action set `A i`, nonnegative finite costs `C i a`, and for each `a ∈ A i` a transition
probability distribution `P i a ·` on the state space. The state space is countable wherever
it is used (`[Countable S]` on the theorems). -/
structure MDC (S : Type) (Act : Type) where
  A : S → Finset Act
  A_nonempty : ∀ i, (A i).Nonempty
  C : S → Act → ℝ≥0
  P : S → Act → S → ℝ≥0∞
  P_sum : ∀ i, ∀ a ∈ A i, ∑' j, P i a j = 1

namespace MDC

variable {S Act : Type} (M : MDC S Act)

/-- A general (history-dependent, randomized) policy (§2.2, pp. 20–22). A history at time `t`
is `h_t = (i_0, a_0, …, i_{t-1}, a_{t-1}, i_t)`; it is encoded as the list of past
state–action pairs, **most recent first**, together with the current state `i_t`.
`σ h i a` is the probability `θ(a | h_t)` of choosing `a`; it is a probability distribution on
`A i`. -/
structure Policy where
  σ : List (S × Act) → S → Act → ℝ≥0∞
  σ_sum : ∀ h i, ∑ a ∈ M.A i, σ h i a = 1
  σ_supp : ∀ h i a, a ∉ M.A i → σ h i a = 0

variable {M}

/-- `histProb θ i t h j` is the probability, under `θ` from initial state `i`, that the history
at time `t` is `(h, j)` (past pairs `h`, most recent first, current state `j`) (§2.3). -/
noncomputable def histProb (θ : M.Policy) (i : S) : ℕ → List (S × Act) → S → ℝ≥0∞
  | 0, [], j => if j = i then 1 else 0
  | 0, _ :: _, _ => 0
  | _ + 1, [], _ => 0
  | t + 1, (k, a) :: h, j => histProb θ i t h k * θ.σ h k a * M.P k a j

/-- `E_θ[C(X_t, A_t) | X_0 = i]`, equation (2.6), p. 23 (a `[0, ∞]`-valued sum). -/
noncomputable def expectedCost (θ : M.Policy) (i : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' h : List (S × Act), ∑' j : S, ∑ a ∈ M.A j,
    histProb θ i t h j * θ.σ h j a * (M.C j a : ℝ≥0∞)

/-- The expected discounted cost `V_{θ,α}(i) = Σ_t α^t E_θ[C(X_t,A_t) | X_0 = i]`,
equation (2.13), p. 26; values in `[0, ∞]`. -/
noncomputable def discCost (θ : M.Policy) (α : ℝ≥0) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, (α : ℝ≥0∞) ^ t * expectedCost θ i t

variable (M)

/-- The discounted value function `V_α(i) = inf_θ V_{θ,α}(i)` over all general policies,
equation (2.14), p. 26. -/
noncomputable def value (α : ℝ≥0) (i : S) : ℝ≥0∞ :=
  ⨅ θ : M.Policy, discCost θ α i

variable {M}

/-- The `n`-horizon expected discounted cost with terminal cost `0`,
`v_{θ,α,n}(i) = Σ_{t<n} α^t E_θ[C(X_t,A_t) | X_0 = i]` (equation (2.9) with `F = 0`, p. 25, 61).
Only the decisions at times `0, …, n-1` enter, so an `n`-horizon policy is the restriction of a
general policy. -/
noncomputable def horizonCost (θ : M.Policy) (α : ℝ≥0) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range n, (α : ℝ≥0∞) ^ t * expectedCost θ i t

variable (M)

/-- The `n`-horizon discounted value function with terminal cost `0`,
`v_{α,n}(i) = inf_θ v_{θ,α,n}(i)`, equation (2.10). -/
noncomputable def horizonValue (α : ℝ≥0) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ⨅ θ : M.Policy, horizonCost θ α n i

/-- The stationary policy `f` (with `f i ∈ A i`) viewed as a general policy: at every history
with current state `i` it chooses `f i` with probability one (§2.2, p. 20). -/
noncomputable def ofStationary (f : S → Act) (hf : ∀ i, f i ∈ M.A i) : M.Policy where
  σ _ i a := if a = f i then 1 else 0
  σ_sum _ i := by simp [hf i]
  σ_supp _ i a ha := by
    have : a ≠ f i := fun h => ha (h ▸ hf i)
    simp [this]

end MDC

end SennottDP.DiscountedASM
