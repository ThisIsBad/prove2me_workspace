import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Proof of Theorem 4 (Zipkin 2008, p. 939): if the continuation `F` (standing for `f̄_{t+1}`) is
L♮-convex and nonnegative on `V`, then for each demand value `d ≥ 0` the end-of-period cost
`κ̄(v, ζ | d)` of (4) is L♮-convex on `V × ℜ⁻`. -/
theorem kappa_lnatconvex (L : ℕ) (hL : 0 < L) (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (F : (Fin L → ℝ) → ℝ) (hF : LNatConvexOn (V L) F)
    (hF0 : ∀ v ∈ V L, 0 ≤ F v) (d : ℝ) (hd : 0 ≤ d) :
    LNatConvexOn (VxNeg L) (liftG (kappa hh p γ F d)) := by sorry

end ZipkinLostSales.LNatural

