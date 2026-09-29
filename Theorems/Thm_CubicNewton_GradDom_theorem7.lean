import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_GradDom_IsGradDominated2
import Definitions.Def_CubicNewton_GradDom_omegaTilde

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Nesterov–Polyak 2006, Theorem 7, p. 194: method (3.3) on a gradient dominated function of
degree `p = 2`. Write `Δ_k = f(x_k) − f(x*)`, `ω̃ = L₀⁴ / (324 (L + L₀)⁶ τ_f³)` (4.14) and
`σ = ω̃^{1/4} / (ω̃^{1/4} + Δ₀^{1/4})`.
1. If `Δ₀ ≥ ω̃` (4.14), then during the first phase — every iteration `k` such that (4.14) holds
   at all earlier iterations `j < k`, i.e. up to and including the first iteration `k₀` at which
   (4.14) fails — `Δ_k ≤ Δ₀ · e^{−kσ}` (4.15).
2. For every `k₀` at which (4.14) fails, i.e. `Δ_{k₀} < ω̃`, and every `k ≥ k₀`:
   `Δ_{k+1} ≤ ω̃ · (Δ_k / ω̃)^{4/3}` (4.16). (The run is monotone, so this is the same as asking
   it from the first such `k₀` on.) -/
theorem theorem7 {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (τ : ℝ) (xs : EuclideanSpace ℝ (Fin n)) (hdom : IsGradDominated2 F f g τ xs)
    (L₀ : ℝ) (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    let ω := omegaTilde L₀ L τ
    let Δ : ℕ → ℝ := fun k => f (x k) - f xs
    let σ := ω ^ (1 / 4 : ℝ) / (ω ^ (1 / 4 : ℝ) + Δ 0 ^ (1 / 4 : ℝ))
    (ω ≤ Δ 0 → ∀ k : ℕ, (∀ j < k, ω ≤ Δ j) → Δ k ≤ Δ 0 * Real.exp (-(k * σ))) ∧
      (∀ k₀ : ℕ, Δ k₀ < ω → ∀ k : ℕ, k₀ ≤ k → Δ (k + 1) ≤ ω * (Δ k / ω) ^ (4 / 3 : ℝ)) := by sorry

end CubicNewton.GradDom

