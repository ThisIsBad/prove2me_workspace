import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_Polars

namespace Disjunctive.Polarity

/-- Theorem 2.18 (Balas §2.4, p. 36): when `F` is full-dimensional, the inequality `αx ≥ α₀`
(with `α₀ ≠ 0`) defines a facet of `cl conv F` if and only if `(α, α₀)` is an extreme ray of
`W₀`. -/
theorem facet_characterization_polarity {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (hdim : PolyDim (DisjunctiveSet m A b) = (n : ℤ)) (α : Fin n → ℝ) (α0 : ℝ) (hα0 : α0 ≠ 0) :
    IsFacet (closure (convexHull ℝ (DisjunctiveSet m A b)))
        (closure (convexHull ℝ (DisjunctiveSet m A b)) ∩ {x | dotProduct α x = α0}) ↔
      IsExtremeRay (W0 m A b) (α, α0) := by sorry

end Disjunctive.Polarity

