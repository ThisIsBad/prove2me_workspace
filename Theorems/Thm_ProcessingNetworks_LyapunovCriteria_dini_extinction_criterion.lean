import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative

namespace ProcessingNetworks.LyapunovCriteria

open MeasureTheory

/-- Lemma 8.11, Dai & Harrison p. 139 (PDF p. 155) — the goal theorem of this mission: assume
`f : ℝ_+ → ℝ_+` satisfies (a) `f` is continuous on `(0,∞)`; (b) for each interval `[a,b) ⊂ ℝ_+`
there is `M > 0` with `D⁺f(t) ≤ M` for all `t ∈ [a,b)` (8.6); (c) there is `ε > 0` such that
`D⁺f(t) ≤ -ε` for almost all `t ∈ ℝ_+` with `f(t) > 0` (8.7). Then `f(t) = 0` for
`t ≥ f(0)/ε`. This generalizes Lemma 8.5 to Lyapunov functions `H` that are merely continuous,
not Lipschitz. -/
theorem dini_extinction_criterion
    (f : ℝ → ℝ) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hbound : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Set.Ico a b, diniUpperRight f t ≤ (M : EReal))
    (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t, 0 ≤ t → 0 < f t → diniUpperRight f t ≤ ((-ε : ℝ) : EReal)) :
    ∀ t : ℝ, f 0 / ε ≤ t → f t = 0 := by sorry

end ProcessingNetworks.LyapunovCriteria
