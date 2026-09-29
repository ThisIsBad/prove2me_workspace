import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Proposition 2.4 (search direction properties), arXiv:1206.1623v13, p. 6. Under the §2
standing assumptions (`g` convex, continuously differentiable, `∇g` Lipschitz with constant `L1`;
`h` proper closed convex with domain `D`), let `x ∈ D`, `H` symmetric positive definite, and `Δ`
the search direction (2.9). Then (2.14) `f(x + tΔ) ≤ f(x) + tλ + O(t²)`, in the form
`∃ C, ∀ t ∈ (0, 1], f(x + tΔ) ≤ f(x) + tλ + C t²`; and (2.15) `λ ≤ −ΔᵀHΔ`. -/
theorem search_direction_properties {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hD : IsProperClosedConvex D h)
    (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ D) (hH : IsPosDef H) (hΔ : IsSearchDirection g D h x H Δ) :
    (∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      compositeObj g D h (x + t • Δ) ≤
        ((g x + h x + t * predDecrease g h x Δ + C * t ^ 2 : ℝ) : EReal)) ∧
    predDecrease g h x Δ ≤ -⟪H Δ, Δ⟫ := by sorry

end ProxNewton.Exact
