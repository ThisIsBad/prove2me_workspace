import Mathlib
import Definitions.Def_SAGA_StronglyConvex_IsProxPoint
import Definitions.Def_SAGA_StronglyConvex_sagaRun

open scoped InnerProductSpace

namespace SAGA.StronglyConvex

/-- Corollary 1 (p. 8; announced on p. 2): linear convergence of SAGA in the strongly convex
composite case. Each `f_i` is `μ`-strongly convex with `L`-Lipschitz gradient `f'_i`, `h` is convex
and real-valued, `P` is the proximal map `prox_γ^h`, `x*` (here `xs`) minimizes
`F = f + h` with `f = (1/n) Σ_i f_i`, and `γ = 1/(2(μn+L))`. SAGA starts at `x^0` with
`φ_i^0 = x^0`. The expectation over the `k` indices, drawn independently and uniformly from the
`n` components, is the average over all `n^k` index sequences. -/
theorem corollary1_linear_convergence {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (μ L : ℝ) (hμ : 0 < μ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hsc : ∀ i, StrongConvexOn Set.univ μ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hh : ConvexOn ℝ Set.univ h)
    (xs : EuclideanSpace ℝ (Fin d))
    (hxs : ∀ y, (1 / (n : ℝ)) * ∑ i, f i xs + h xs ≤ (1 / (n : ℝ)) * ∑ i, f i y + h y)
    (γ : ℝ) (hγ : γ = 1 / (2 * (μ * n + L)))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h γ y (P y))
    (x0 : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    (1 / (n : ℝ) ^ k) * ∑ js : Fin k → Fin n, ‖(sagaRun f' P γ x0 k js).1 - xs‖ ^ 2 ≤
      (1 - μ / (2 * (μ * n + L))) ^ k *
        (‖x0 - xs‖ ^ 2 + n / (μ * n + L) *
          ((1 / (n : ℝ)) * ∑ i, f i x0 - ⟪(1 / (n : ℝ)) • ∑ i, f' i xs, x0 - xs⟫_ℝ
            - (1 / (n : ℝ)) * ∑ i, f i xs)) := by sorry

end SAGA.StronglyConvex

