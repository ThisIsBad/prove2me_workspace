import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaStep
import Definitions.Def_SAGA_Convex_sagaRun

open scoped RealInnerProductSpace

namespace SAGA.Convex

/-- Theorem 2 (Appendix C, p. 11): each `fᵢ` convex with `L`-Lipschitz gradient, `h` convex,
`x*` a minimizer of `F = f + h`, SAGA run with `γ = 1/(3L)` and `P = prox_γ^h` from `x^0`
(with `φᵢ^0 = x^0`). For every `k ≥ 1`, with `x̄^k = (1/k) ∑_{t=1}^k x^t` and `E` over the `k`
independent uniform indices,
`E[F(x̄^k)] - F(x*) ≤ (4n/k) [(2L/n)‖x^0 - x*‖² + f(x^0) - ⟨f′(x*), x^0 - x*⟩ - f(x*)]`. -/
theorem saga_averaged_iterate_rate {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h (1 / (3 * L)) y (P y))
    (xs : EuclideanSpace ℝ (Fin d)) (hopt : ∀ y, fAvg f xs + h xs ≤ fAvg f y + h y)
    (x0 : EuclideanSpace ℝ (Fin d)) (k : ℕ) (hk : 1 ≤ k) :
    expectIdx n k (fun js => fAvg f (avgIterate f' P (1 / (3 * L)) x0 js)
        + h (avgIterate f' P (1 / (3 * L)) x0 js))
      - (fAvg f xs + h xs) ≤
      4 * n / k * (2 * L / n * ‖x0 - xs‖ ^ 2 + fAvg f x0 - ⟪gradAvg f' xs, x0 - xs⟫
        - fAvg f xs) := by sorry

end SAGA.Convex

