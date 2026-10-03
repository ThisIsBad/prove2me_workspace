import Mathlib
import Definitions.Def_SennottDP_AvgASM_Model

namespace SennottDP.AvgASM

open scoped ENNReal NNReal
open Filter

variable {S : Type*} {Act : Type*} [Countable S]

/-- The `n`-horizon expected cost with terminal cost `0` and no discounting,
`v_{θ,n}(i) = ∑_{t=0}^{n-1} E_θ[C(X_t,A_t) | X_0 = i]` ((2.11) with `α = 1`, `F = 0`), in `[0, ∞]`. -/
noncomputable def horizonCost {M : MDC S Act} (θ : Policy M) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range n, expCost θ i t

/-- The `n`-horizon value function `v_n(i) = inf_θ v_{θ,n}(i)` over all general policies
(terminal cost `0`, `α = 1`; (2.12), p. 26). -/
noncomputable def horizonValue (M : MDC S Act) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ⨅ θ : Policy M, horizonCost θ n i

/-- The expected discounted cost `V_{θ,α}(i) = ∑_{t ≥ 0} α^t E_θ[C(X_t,A_t) | X_0 = i]` (2.13),
p. 26, valued in `[0, ∞]` (used for `α ∈ (0, 1)`). -/
noncomputable def discCost {M : MDC S Act} (θ : Policy M) (α : ℝ) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, ENNReal.ofReal α ^ t * expCost θ i t

/-- The discounted value function `V_α(i) = inf_θ V_{θ,α}(i)` over all general policies (2.14),
p. 26. -/
noncomputable def discValue (M : MDC S Act) (α : ℝ) (i : S) : ℝ≥0∞ :=
  ⨅ θ : Policy M, discCost θ α i

/-- The long-run expected average cost `J_θ(i) = limsup_{n→∞} v_{θ,n}(i)/n` (2.15), p. 27,
in `[0, ∞]`. -/
noncomputable def avgCost {M : MDC S Act} (θ : Policy M) (i : S) : ℝ≥0∞ :=
  limsup (fun n : ℕ => horizonCost θ n i / (n : ℝ≥0∞)) atTop

/-- The minimum average cost `J(i) = inf_θ J_θ(i)` over all general policies (2.16), p. 27. -/
noncomputable def avgValue (M : MDC S Act) (i : S) : ℝ≥0∞ :=
  ⨅ θ : Policy M, avgCost θ i

/-- Definition 2.4.5: `θ` is average cost optimal if `J_θ(i) = J(i)` for all `i`. -/
def IsAverageOptimal {M : MDC S Act} (θ : Policy M) : Prop :=
  ∀ i, avgCost θ i = avgValue M i

end SennottDP.AvgASM
