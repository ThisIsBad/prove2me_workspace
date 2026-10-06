import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaStep
import Definitions.Def_SAGA_Convex_lyapunov

namespace SAGA.Convex

/-- Appendix C, p. 12 (one-step decrease): each `fᵢ` convex with `L`-Lipschitz gradient, `h`
convex, `x*` a minimizer of `F = f + h`, step `γ = 1/(3L)`, `P = prox_γ^h`, and the Lyapunov
function `T` with coefficient `c + α = 3L/(2n) + 3L/(8n)` on `‖x - x*‖²`. For every state
`(x^k, φ^k)`, with `E` the average over the uniformly drawn index `j`,
`E[T^{k+1}] - T^k ≤ -(1/(4n)) E[F(x^{k+1}) - F(x*)]`. -/
theorem lyapunov_one_step {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h (1 / (3 * L)) y (P y))
    (xs : EuclideanSpace ℝ (Fin d)) (hopt : ∀ y, fAvg f xs + h xs ≤ fAvg f y + h y)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) :
    (1 / (n : ℝ)) * ∑ j, lyapunov f f' xs (3 * L / (2 * n) + 3 * L / (8 * n))
        (sagaStep f' P (1 / (3 * L)) s j)
      - lyapunov f f' xs (3 * L / (2 * n) + 3 * L / (8 * n)) s ≤
      -(1 / (4 * (n : ℝ))) * ((1 / (n : ℝ)) * ∑ j,
          ((fAvg f (sagaStep f' P (1 / (3 * L)) s j).1 + h (sagaStep f' P (1 / (3 * L)) s j).1)
            - (fAvg f xs + h xs))) := by sorry

end SAGA.Convex

