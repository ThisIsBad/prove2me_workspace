import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_Nonconvex_muMeasure

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

/-- Nesterov–Polyak 2006, Theorem 1, inequality (3.4), p. 185: along every run of method (3.3),
for every `k ≥ 1`,
`min_{1 ≤ i ≤ k} μ_L(x_i) ≤ (8/3)·(3(f(x₀) − f*)/(2k·L₀))^{1/3}`.
The minimum over the finite index set is written as the existence of an index attaining the bound. -/
theorem min_mu_rate {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (L₀ : ℝ) (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L)
    (fstar : ℝ) (hfstar : ∀ y ∈ F, fstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ i, 1 ≤ i ∧ i ≤ k ∧
      muMeasure L L g H (x i) ≤ 8 / 3 * (3 * (f x₀ - fstar) / (2 * k * L₀)) ^ (1 / 3 : ℝ) := by sorry

end CubicNewton.Nonconvex
