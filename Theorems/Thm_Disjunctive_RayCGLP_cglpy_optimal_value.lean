import Mathlib
import Definitions.Def_Disjunctive_RayCGLP_Basic

namespace Disjunctive.RayCGLP

/-- Theorem 10.3 (Balas §10.6, p. 138, [32]), the goal theorem of this mission: if `(CGLP)_y` has
an optimal solution `(α̃,β̃)`, then `x̄ᵀα̃ - β̃ = -λ*` with `λ* := min{λ : x̄ + yλ ∈ P_D}`, and
`(x̄ + yλ*)ᵀα̃ = β̃`.

The page's display prints `x̄ᵀα̃ - β̃ = λ*`; its own proof computes `x̄ᵀα̃ - β̃ = -λ₀` and then
`λ₀ = λ*`, so the sign of the proof is the one taken here (`P_D = {(3,t) : |t| ≤ 1}`, `x̄ = 0`,
`y = (1,0)` has optimum `α = (1,0)`, `β = 3`, hence `αx̄ - β = -3` while `λ* = 3`). `λ*` is a
*minimum*, and `P_D` a closed convex set, as on the page: for `P_D = {(3,1), (3,-1)}` the set of
`λ` is empty and a real infimum of the empty set would read `0`. -/
theorem cglpy_optimal_value {n : ℕ} (PD : Set (Fin n → ℝ)) (hPDconv : Convex ℝ PD)
    (hPDclosed : IsClosed PD) (y xbar : Fin n → ℝ)
    (alphaT : Fin n → ℝ) (betaT : ℝ) (hopt : IsCGLPYOptimal PD y xbar alphaT betaT)
    (lamStar : ℝ) (hlam : IsLeast {lam : ℝ | xbar + lam • y ∈ PD} lamStar) :
    dotProduct alphaT xbar - betaT = -lamStar ∧
      dotProduct alphaT (xbar + lamStar • y) = betaT := by sorry

end Disjunctive.RayCGLP

