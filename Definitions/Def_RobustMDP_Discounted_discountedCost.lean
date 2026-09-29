import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model

namespace RobustMDP.Discounted

/-- The distribution of the state `i_t` at time `t` under a stationary controller policy `π`
and stationary transition matrices `P` (`P a i j` = probability of moving from `i` to `j` under
action `a`), starting from the initial state `i₀`: `μ_0 = e_{i₀}` and
`μ_{t+1}(j) = ∑_i μ_t(i) P^{𝐚(i)}(i, j)`. -/
noncomputable def stateDist {n : ℕ} {A : Type} (π : StationaryPolicy n A)
    (P : A → Fin n → Fin n → ℝ) (i₀ : Fin n) : ℕ → Fin n → ℝ
  | 0 => fun j => if j = i₀ then 1 else 0
  | t + 1 => fun j => ∑ i, stateDist π P i₀ t i * P (π i) i j

/-- The discounted cost `C_∞(π, τ)` (p. 781): the expected total cost (2) with stage costs
`c_t(i, a) = ν^t c(i, a)` and zero terminal cost, in the limit `N → ∞`, from the initial state
`i₀`, for a stationary policy `π` and a stationary nature policy `P ∈ 𝒯_s`:
`C_∞(π, P) = ∑_{t ≥ 0} ν^t ∑_i μ_t(i) c(i, 𝐚(i))`, with `μ_t = stateDist π P i₀ t`.
It is written as a `tsum`; its terms are nonnegative and bounded by `ν^t max c` (each `μ_t` is a
probability vector), so the series is summable and the `tsum` is the limit of the `N`-stage
costs, which is the paper's definition. -/
noncomputable def Model.discountedCost {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n)
    (π : StationaryPolicy n A) (P : M.StationaryNature) : ℝ :=
  ∑' t : ℕ, M.discount ^ t * ∑ i, stateDist π P.1 i₀ t i * M.cost i (π i)

end RobustMDP.Discounted
