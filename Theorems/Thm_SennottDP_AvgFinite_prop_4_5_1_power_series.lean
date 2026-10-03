import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Criteria

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal

/-- Proposition 4.5.1 (Sennott, p. 70). For a policy `θ` and an initial state `i`, the power series
(4.24) `V_{θ,α}(i) = ∑_n α^n u_n`, `u_n = E_θ[C(X_n,A_n) | X_0 = i]`, `α ∈ [0,∞)`, has a radius of
convergence `R_i ∈ [0,∞]` (it converges for `0 ≤ α < R_i` and diverges for `α > R_i`), and if
`R_i > 0` then `α ↦ V_{θ,α}(i)` is infinitely differentiable on `(0, R_i)`. -/
theorem prop_4_5_1_power_series {S : Type*} {Act : Type*} [Countable S] (M : MDC S Act)
    (θ : Policy M) (i : S) :
    ∃ R : ℝ≥0∞,
      (∀ α : ℝ, 0 ≤ α → ENNReal.ofReal α < R → discCost θ α i ≠ ⊤) ∧
      (∀ α : ℝ, R < ENNReal.ofReal α → discCost θ α i = ⊤) ∧
      (0 < R → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun α : ℝ => (discCost θ α i).toReal)
        {α : ℝ | 0 < α ∧ ENNReal.ofReal α < R}) := by sorry

end SennottDP.AvgFinite
