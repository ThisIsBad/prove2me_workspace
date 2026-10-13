import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Lemma 7.4.1, p. 140. Let `z` be a distinguished state and `α ∈ (0,1)` with
`V_α(z) < ∞`. If `i ≠ z` and `θ ∈ ℜ*(i,z)`, then `h_α(i) ≤ c_{iz}(θ)`. Hence, if `V_α(z) < ∞`
for every `α ∈ (0,1)` and every `i ≠ z` has a policy `θ_i ∈ ℜ*(i,z)`, then (SEN2) holds for `z`
with `M(i) = c_{iz}(θ_i)` for `i ≠ z` and `M(z) = 0`. -/
theorem relValue_le_passageCost {S Act : Type} [Countable S] [DecidableEq S] (M : SennottDP.Discounted.MDC S Act) (z : S) :
    (∀ α : ℝ, 0 < α → α < 1 → valueFn M α z < ⊤ →
      ∀ i, i ≠ z → ∀ θ : SennottDP.Discounted.Policy M, InRStar θ i {z} →
        relValue M z α i ≤ ((passageCost θ i {z} : ℝ≥0∞) : EReal)) ∧
    ((∀ α : ℝ, 0 < α → α < 1 → valueFn M α z < ⊤) →
      ∀ θ : S → SennottDP.Discounted.Policy M, (∀ i, i ≠ z → InRStar (θ i) i {z}) →
        SEN2 M z (fun i => if i = z then 0 else (passageCost (θ i) i {z}).toReal)) := by sorry

end SennottDP.BOR

