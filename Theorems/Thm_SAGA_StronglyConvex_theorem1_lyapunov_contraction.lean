import Mathlib
import Definitions.Def_SAGA_StronglyConvex_IsProxPoint
import Definitions.Def_SAGA_StronglyConvex_sagaStep
import Definitions.Def_SAGA_StronglyConvex_lyapunov

namespace SAGA.StronglyConvex

/-- Theorem 1 (p. 7). Each `f_i` is `μ`-strongly convex with `L`-Lipschitz gradient `f'_i`, `h` is
convex and real-valued, `P` is the proximal map `prox_γ^h` (every `P y` minimizes (3)), and `x*`
(here `xs`) minimizes `F = (1/n) Σ_i f_i + h`. With `γ = 1/(2(μn+L))`, `c = 1/(2γ(1-γμ)n)` and
`κ = 1/(γμ)`, for every state `(x, φ)` the average of the Lyapunov function `T` over the next
SAGA state (index `j` uniform on the `n` components) is at most `(1 - 1/κ) T(x, φ)`. -/
theorem theorem1_lyapunov_contraction {d n : ℕ} (hn : 0 < n)
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
    (γ c κ : ℝ) (hγ : γ = 1 / (2 * (μ * n + L))) (hc : c = 1 / (2 * γ * (1 - γ * μ) * n))
    (hκ : κ = 1 / (γ * μ))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h γ y (P y))
    (x : EuclideanSpace ℝ (Fin d)) (φ : Fin n → EuclideanSpace ℝ (Fin d)) :
    (1 / (n : ℝ)) * ∑ j, lyapunov f f' c xs (sagaStep f' P γ (x, φ) j) ≤
      (1 - 1 / κ) * lyapunov f f' c xs (x, φ) := by sorry

end SAGA.StronglyConvex

