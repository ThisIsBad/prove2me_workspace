import Mathlib

namespace TeschlODE.Horseshoe

/-- Teschl, §13.1, p. 332, (13.5)–(13.6): the inverse `g = f⁻¹` of the horseshoe map on
`K₀ = f(J₀) = [0, λ] × [0, 1]` and `K₁ = f(J₁) = [1 − λ, 1] × [0, 1]`:
`g(x, y) = (λ⁻¹x, µ⁻¹y)` on `K₀` (13.5) and `g(x, y) = (λ⁻¹(1 − x), 1 − µ⁻¹y)` on `K₁` (13.6).
Here the first formula is used whenever `x ≤ λ` and the second otherwise; for `λ < 1/2` the
strips `K₀`, `K₁` are disjoint, and the values off `K₀ ∪ K₁` carry no meaning. -/
noncomputable def horseshoeInv (lam μ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if p.1 ≤ lam then (lam⁻¹ * p.1, μ⁻¹ * p.2) else (lam⁻¹ * (1 - p.1), 1 - μ⁻¹ * p.2)

end TeschlODE.Horseshoe
