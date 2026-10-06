import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model

namespace FedergruenZipkin.AvgCost
open scoped ENNReal
theorem lemma4_reachability (M : Model) (U L : ℤ) (Dm Dp : ℕ)
    (hDm : 0 < M.p Dm ∧ ∀ j < Dm, M.p j = 0)
    (hDp : Dm < Dp ∧ 0 < M.p Dp ∧ ∀ j, Dm < j → j < Dp → M.p j = 0)
    (hL : L < U - M.b) (hUL : max (M.b : ℤ) ((Dm : ℤ) + Dp) ≤ U - L) :
    ∀ x' : ℤ, L ≤ x' → x' ≤ U - Dm → ∃ δ : ℤ → ℤ, FeasibleL M U L δ ∧
      ∀ x₀ : ℤ, L ≤ x₀ → x₀ ≤ U - Dm → ∃ n : ℕ, 0 < (P M δ)^[n] (Set.indicator {x'} 1) x₀ := by sorry
end FedergruenZipkin.AvgCost

