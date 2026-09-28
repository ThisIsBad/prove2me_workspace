import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_gradNormMax

namespace BiconvexProg.BranchBound

/-- Gradient bound (p. 281). Let `γ = max {‖∇(xy)‖ : (x, y) ∈ [l, L] × [m, M]}` (Euclidean norm,
`∇(xy) = (y, x)`). Then `γ = ‖(β, α)‖` for a corner `(α, β)` of the rectangle, and for every
sub-rectangle `[l', L'] × [m', M']` the gradients `(m', l')` of `h₁ = m'x + l'y − l'm'` and
`(M', L')` of `h₂ = M'x + L'y − L'M'` have Euclidean norm at most `γ`. -/
theorem grad_bound (l L m M : ℝ) (hlL : l ≤ L) (hmM : m ≤ M) :
    (∃ α ∈ ({l, L} : Set ℝ), ∃ β ∈ ({m, M} : Set ℝ),
      gradNormMax l L m M = Real.sqrt (β ^ 2 + α ^ 2)) ∧
    ∀ l' L' m' M' : ℝ, l ≤ l' → l' ≤ L' → L' ≤ L → m ≤ m' → m' ≤ M' → M' ≤ M →
      Real.sqrt (m' ^ 2 + l' ^ 2) ≤ gradNormMax l L m M ∧
        Real.sqrt (M' ^ 2 + L' ^ 2) ≤ gradNormMax l L m M := by sorry

end BiconvexProg.BranchBound
