import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model
import Definitions.Def_RobustMDP_Discounted_discountedCost

namespace RobustMDP.Discounted

/-- Linear program (26) (Nilim–El Ghaoui 2005, p. 786). For a stationary controller policy
`π = (𝐚, 𝐚, …)` and a fixed stationary nature policy `P ∈ 𝒯_s`, the discounted cost
`C_∞(π, P)` from the initial state `i₀` is the optimal value of
`max_v qᵀ v  s.t.  v(i) ≤ c(i, 𝐚(i)) + ν ∑_j P^{𝐚(i)}(i, j) v(j), i ∈ 𝒳`,
with `q = e_{i₀}` (so `qᵀ v = v(i₀)`), and the maximum is attained. -/
theorem discountedCost_lp {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n)
    (π : StationaryPolicy n A) (P : M.StationaryNature) :
    IsGreatest
      ((fun v : Fin n → ℝ => v i₀) ''
        {v | ∀ i, v i ≤ M.cost i (π i) + M.discount * ∑ j, P.1 (π i) i j * v j})
      (M.discountedCost i₀ π P) := by sorry

end RobustMDP.Discounted
