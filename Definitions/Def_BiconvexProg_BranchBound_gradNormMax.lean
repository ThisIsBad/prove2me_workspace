import Mathlib

namespace BiconvexProg.BranchBound

/-- The maximum-norm value `γ = max {‖∇(xy)‖ : l ≤ x ≤ L, m ≤ y ≤ M}` of p. 281: since
`∇(xy) = (y, x)`, it is the supremum of the Euclidean norm `√(y² + x²)` over the rectangle.
Junk value: `0` if the rectangle is empty (`L < l` or `M < m`). -/
noncomputable def gradNormMax (l L m M : ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => Real.sqrt (p.2 ^ 2 + p.1 ^ 2)) '' (Set.Icc l L ×ˢ Set.Icc m M))

/-- The Euclidean distance on `ℝⁿ × ℝⁿ = ℝ²ⁿ`:
`‖(x, y) − (u, v)‖ = √(∑ᵢ ((xᵢ − uᵢ)² + (yᵢ − vᵢ)²))`. (Mathlib's default metric on these
types is the sup metric, so the Euclidean one is written out.) -/
noncomputable def eucDist {n : ℕ} (z w : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  Real.sqrt (∑ i, ((z.1 i - w.1 i) ^ 2 + (z.2 i - w.2 i) ^ 2))

end BiconvexProg.BranchBound
