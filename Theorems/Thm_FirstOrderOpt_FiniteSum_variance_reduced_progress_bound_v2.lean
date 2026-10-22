import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction


namespace FirstOrderOpt.FiniteSum

open FirstOrderOpt.Prox

/-- Lemma 5.14 (one-step progress bound, Eq. (5.3.10)), Lan p. 280. Let `X` be closed convex, `ν`
a distance generating function on `X` with prox-function `V = ν.V`, `Ψ = f + h` with `h` convex
and `f` differentiable with `L`-Lipschitz gradient `∇f` satisfying the generalized strong
convexity (5.3.2) `f(y) ≥ f(x) + ⟨∇f(x), y - x⟩ + μ V(x, y)` with `μ ≥ 0`. If the stepsize
satisfies `Lγ ≤ 1/2` and `xt1` minimizes `u ↦ γ[⟨Gt, u⟩ + h(u)] + V(xt, u)` over `X` (the update
of Algorithm 5.6), then for every `x ∈ X`,
`γ[Ψ(xt1) - Ψ(x)] + V(xt1, x) ≤ (1 - γμ) V(xt, x) + γ⟨δt, x - xt⟩ + γ² ‖δt‖²_*`,
where `δt := Gt - ∇f(xt)`.

Corrected version: `V` is the Bregman distance of a distance generating function (the retired
free `V` left `V(xt1, x)` unconstrained), `∇f` is the gradient of `f`, `h` is convex and `X` is
closed convex. The lemma holds for every `μ ≥ 0`, as in the book. -/
theorem variance_reduced_progress_bound_v2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x) (hhconv : ConvexOn ℝ X h)
    (gradf_full : E → E →L[ℝ] ℝ)
    (hgrad : ∀ x, HasFDerivAt f (gradf_full x) x)
    (L : ℝ) (hL : 0 < L) (hsmooth : ∀ x y, ‖gradf_full x - gradf_full y‖ ≤ L * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hstrong : ∀ x ∈ X, ∀ y ∈ X, f y ≥ f x + (gradf_full x) (y - x) + μ * ν.V x y)
    (γ : ℝ) (hγ : 0 < γ) (hLγ : L * γ ≤ 1 / 2)
    (xt xt1 : E) (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (Gt δt : E →L[ℝ] ℝ) (hδt : δt = Gt - gradf_full xt)
    (hmin : ∀ y ∈ X, γ * (Gt xt1) + γ * h xt1 + ν.V xt xt1 ≤ γ * (Gt y) + γ * h y + ν.V xt y) :
    ∀ x ∈ X, γ * (Ψ xt1 - Ψ x) + ν.V xt1 x ≤
      (1 - γ * μ) * ν.V xt x + γ * (δt (x - xt)) + γ ^ 2 * ‖δt‖ ^ 2 := by sorry

end FirstOrderOpt.FiniteSum

