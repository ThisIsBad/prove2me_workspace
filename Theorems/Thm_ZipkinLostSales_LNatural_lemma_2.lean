import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Lemma 2 (Zipkin 2008, p. 939): if `g(v, ζ)` is L♮-convex on `V × ℜ⁻`, so is
`f(v) = min_{ζ ≤ 0} g(v, ζ)` on `V`. The "min" is the infimum over `ζ ≤ 0`, assumed bounded
below for every `v ∈ V`. -/
theorem lemma_2 (L : ℕ) (hL : 0 < L) (g : (Fin L → ℝ) → ℝ → ℝ)
    (hg : LNatConvexOn (VxNeg L) (liftG g))
    (hbdd : ∀ v ∈ V L, BddBelow (g v '' Set.Iic 0)) :
    LNatConvexOn (V L) (fun v => ⨅ ζ : Set.Iic (0 : ℝ), g v ζ) := by sorry

end ZipkinLostSales.LNatural

