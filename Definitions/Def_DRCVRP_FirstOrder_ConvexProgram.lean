import Mathlib

namespace DRCVRP.FirstOrder

/-!
The optimization problem (13) of Ghosal and Wiesemann, *The Distributionally Robust
Chance-Constrained Vehicle Routing Problem*, Oper. Res. 68(3) (2020), §5.1, p. 726, Theorem 5.
Customers are `Fin n` (0-based), the customer subsets `S_1, …, S_p` are `Sfam : Fin p → Finset
(Fin n)`, and `γ : Fin p → ℝ` is the decision vector of (13).
-/

/-- The vector `q̂ = min {(q̄ − μ), ((1 − ε)/ε)(μ − q̲)}`, minimum taken componentwise
(§5.1, p. 726, Theorem 5, Corollaries 2 and 3). -/
noncomputable def qhat {n : ℕ} (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (j : Fin n) : ℝ :=
  min (qhi j - μ j) ((1 - ε) / ε * (μ j - qlo j))

/-- The objective function of problem (13) (§5.1, p. 726):
`1_Sᵀ μ + min {(q̄ − μ), ((1 − ε)/ε)(μ − q̲)}ᵀ · [1_S − 2 ∑_{l=1}^p γ_l 1_{S_l}]₊ + (1/ε) νᵀ γ`.
The positive part `[·]₊` is taken componentwise, and the inner product runs over all customers
`j ∈ V_C`. -/
noncomputable def convexProgramObjective {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (Sfam : Fin p → Finset (Fin n)) (ν : Fin p → ℝ) (ε : ℝ) (S : Finset (Fin n))
    (γ : Fin p → ℝ) : ℝ :=
  ∑ j ∈ S, μ j +
    ∑ j, qhat qlo qhi μ ε j *
      max 0 ((if j ∈ S then 1 else 0) - 2 * ∑ l, γ l * (if j ∈ Sfam l then 1 else 0)) +
    (1 / ε) * ∑ l, ν l * γ l

end DRCVRP.FirstOrder
