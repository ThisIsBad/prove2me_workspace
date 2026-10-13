import Mathlib
import Definitions.Def_SennottDP_SEN_MDC
import Definitions.Def_SennottDP_Discounted_Criteria

open scoped ENNReal NNReal
open Filter

namespace SennottDP.SEN

variable {S : Type} [Countable S] {Act : Type}

open Classical in

open Classical in
/-- The distribution of the state at time `n`: `P_θ(X_n = j | X_0 = i)`, the total probability of
the histories of length `n` that end in `j`. -/
noncomputable def stateProb (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M) (i : S) (n : ℕ) (j : S) : ℝ≥0∞ :=
  ∑' s : Fin (n + 1) → S, ∑' as : Fin n → Act,
    if s (Fin.last n) = j then SennottDP.Discounted.histProb M θ i n s as else 0

/-- The sum `∑_j p(j) h(j)` of a real function `h` against nonnegative weights `p`, as an extended
real: the sum of the positive parts minus the sum of the negative parts,
`∑_j p(j) h(j)^+ − ∑_j p(j) h(j)^-`, each computed in `[0, ∞]`. When the negative part is finite
(for instance when `h` is bounded below and `p` is a probability) this is the usual value in
`(−∞, +∞]`; when both parts are `+∞` the `EReal` convention `⊤ − ⊤ = ⊥` gives `−∞`. -/
noncomputable def wsum (p : S → ℝ≥0∞) (h : S → ℝ) : EReal :=
  ((∑' j, p j * ENNReal.ofReal (h j) : ℝ≥0∞) : EReal) -
    ((∑' j, p j * ENNReal.ofReal (-h j) : ℝ≥0∞) : EReal)

/-- The expectation `E_θ[h(X_n) | X_0 = i]` of a real function `h` of the state at time `n`, as an
extended real computed by `wsum` from the distribution of `X_n`. -/
noncomputable def expReal (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M) (i : S) (n : ℕ) (h : S → ℝ) : EReal :=
  wsum (stateProb M θ i n) h

/-- Sennott (1999), (2.11), p. 25, with terminal cost `0` (p. 128: "In this chapter finite horizon
value functions will assume a terminal cost of 0"): the `n`-horizon expected cost
`v_{θ,n}(i) = ∑_{t=0}^{n-1} E_θ[C(X_t,A_t) | X_0 = i]`, a value in `[0, ∞]`. -/
noncomputable def horizonCost (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range n, SennottDP.Discounted.expCost M θ i t

/-- Sennott (1999), (2.15), p. 27: the long-run expected average cost
`J_θ(i) = limsup_{n→∞} v_{θ,n}(i)/n`, a value in `[0, ∞]`. -/
noncomputable def avgCost (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M) (i : S) : ℝ≥0∞ :=
  limsup (fun n : ℕ => horizonCost M θ n i / (n : ℝ≥0∞)) atTop

/-- Sennott (1999), (2.16), p. 27: the minimum average cost `J(i) = inf_θ J_θ(i)`, the infimum
over all (general) policies. -/
noncomputable def avgValue (M : SennottDP.Discounted.MDC S Act) (i : S) : ℝ≥0∞ :=
  ⨅ θ : SennottDP.Discounted.Policy M, avgCost M θ i

/-- Sennott (1999), Definition 2.4.5, p. 27: a policy `θ` is average cost optimal if
`J_θ(i) = J(i)` for every `i ∈ S`. -/
def IsAverageOptimal (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M) : Prop :=
  ∀ i, avgCost M θ i = avgValue M i

/-- Sennott (1999), (2.13), p. 26: the expected discounted cost
`V_{θ,α}(i) = ∑_{t=0}^∞ α^t E_θ[C(X_t,A_t) | X_0 = i]`, a value in `[0, ∞]` (the book uses
`α ∈ (0,1)`; the real `α` enters through `ENNReal.ofReal`). -/
noncomputable def discCost (M : SennottDP.Discounted.MDC S Act) (θ : SennottDP.Discounted.Policy M) (α : ℝ) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, ENNReal.ofReal α ^ t * SennottDP.Discounted.expCost M θ i t

/-- Sennott (1999), (2.14), p. 26: the discounted value function `V_α(i) = inf_θ V_{θ,α}(i)`,
the infimum over all (general) policies. -/
noncomputable def discValue (M : SennottDP.Discounted.MDC S Act) (α : ℝ) (i : S) : ℝ≥0∞ :=
  ⨅ θ : SennottDP.Discounted.Policy M, discCost M θ α i

end SennottDP.SEN
