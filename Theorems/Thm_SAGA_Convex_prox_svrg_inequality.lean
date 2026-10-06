import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaStep

namespace SAGA.Convex

/-- Appendix C, p. 12 (the prox-SVRG inequality of Xiao–Zhang, applied to SAGA): each `fᵢ`
convex with `L`-Lipschitz gradient, `h` convex, `x*` a minimizer of `F = f + h`, step
`γ = 1/(3L)`, `P = prox_γ^h`. For every state `(x^k, φ^k)` and every `α > 0`, with `E` the
average over the uniformly drawn index `j`,
`α E‖x^{k+1} - x*‖² ≤ α ‖x^k - x*‖² - 2αγ E[F(x^{k+1}) - F(x*)] + 2αγ² E‖Δ‖²`. -/
theorem prox_svrg_inequality {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h (1 / (3 * L)) y (P y))
    (xs : EuclideanSpace ℝ (Fin d)) (hopt : ∀ y, fAvg f xs + h xs ≤ fAvg f y + h y)
    {α : ℝ} (hα : 0 < α)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) :
    α * ((1 / (n : ℝ)) * ∑ j, ‖(sagaStep f' P (1 / (3 * L)) s j).1 - xs‖ ^ 2) ≤
      α * ‖s.1 - xs‖ ^ 2
        - 2 * α * (1 / (3 * L)) * ((1 / (n : ℝ)) * ∑ j,
            ((fAvg f (sagaStep f' P (1 / (3 * L)) s j).1 + h (sagaStep f' P (1 / (3 * L)) s j).1)
              - (fAvg f xs + h xs)))
        + 2 * α * (1 / (3 * L)) ^ 2 *
            ((1 / (n : ℝ)) * ∑ j, ‖sagaDelta f' (1 / (3 * L)) s j‖ ^ 2) := by sorry

end SAGA.Convex

