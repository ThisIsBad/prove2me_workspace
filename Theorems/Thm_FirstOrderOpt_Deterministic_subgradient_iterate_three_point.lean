import Mathlib

namespace FirstOrderOpt.Deterministic

open scoped RealInnerProductSpace

/-- Lemma 3.1 (three-point inequality for the projected-subgradient update). Given `xt` and a
subgradient `gt` of `f` at `xt`, `xt1` minimizes `x ↦ γt⟨gt,x⟩ + ‖x-xt‖²/2` over `X` (the
equivalent form (3.1.4) of the update (3.1.3)); then for every `x ∈ X`, `γt⟨gt, xt1-x⟩ +
‖xt1-xt‖²/2 ≤ ‖x-xt‖²/2 - ‖x-xt1‖²/2`. The book's own statement quantifies over `y ∈ X` but uses
`x` in the body — read here as a single free variable `x ∈ X`, per the erratum recorded in
`STATUS.md`. -/
theorem subgradient_iterate_three_point {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (xt xt1 gt : E) (γt : ℝ)
    (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * ⟪gt, xt1⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      γt * ⟪gt, x⟫ + (1 / 2) * ‖x - xt‖ ^ 2) :
    ∀ x ∈ X, γt * ⟪gt, xt1 - x⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      (1 / 2) * ‖x - xt‖ ^ 2 - (1 / 2) * ‖x - xt1‖ ^ 2 := by sorry

end FirstOrderOpt.Deterministic
