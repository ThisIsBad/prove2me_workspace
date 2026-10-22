import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Lemma 1 (Zipkin 2008, p. 938): if `f(v)` is L♮-convex on `V`, so is
`ψ(v, ζ) = f(v − ζe)` on `V × ℜ⁻`. -/
theorem lemma_1 (L : ℕ) (hL : 0 < L) (f : (Fin L → ℝ) → ℝ) (hf : LNatConvexOn (V L) f) :
    LNatConvexOn (VxNeg L) (liftG (fun v ζ => f (fun i => v i - ζ))) := by sorry

end ZipkinLostSales.LNatural

