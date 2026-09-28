import Mathlib
open scoped RealInnerProductSpace

namespace LogRegretOCO.ONS

/-- Lemma 3 (Hazan–Agarwal–Kale 2007, p. 177). Let `P` have diameter at most `D`, let `f` be
differentiable at every point of `P` with `‖∇f(x)‖ ≤ G` there, and let `exp(−α f)` be concave on
`P`. Then for every `0 < β ≤ ½ min{1/(4GD), α}` and all `x, y ∈ P`,
`f(x) ≥ f(y) + ∇f(y)ᵀ(x − y) + (β/2) (x − y)ᵀ ∇f(y) ∇f(y)ᵀ (x − y)`.
`0 < G`, `0 < D` are the non-degeneracy the formula `1/(4GD)` presupposes; `0 < β` excludes the
degenerate step size (the proof divides by `β`). -/
theorem exp_concave_quadratic_lower_bound {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (G D α β : ℝ) (hG : 0 < G) (hD : 0 < D)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ∀ x ∈ P, DifferentiableAt ℝ f x)
    (hgrad : ∀ x ∈ P, ‖gradient f x‖ ≤ G)
    (hexp : ConcaveOn ℝ P (fun x => Real.exp (-α * f x)))
    (hβ_pos : 0 < β) (hβ : β ≤ (1 / 2) * min (1 / (4 * G * D)) α) :
    ∀ x ∈ P, ∀ y ∈ P,
      f y + ⟪gradient f y, x - y⟫ + (β / 2) * ⟪gradient f y, x - y⟫ ^ 2 ≤ f x := by sorry

end LogRegretOCO.ONS

