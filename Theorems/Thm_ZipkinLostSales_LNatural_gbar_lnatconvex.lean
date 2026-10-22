import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Proof of Theorem 4 (Zipkin 2008, p. 939): if `f̄_{t+1}` (here `fbar … k`) is L♮-convex on `V`,
then `ḡ_t(v, ζ) = −γ^L c ζ + E_d[κ̄_t(v, ζ | d)]` (here `gbar … k`) is L♮-convex on `V × ℜ⁻`. -/
theorem gbar_lnatconvex (L : ℕ) (hL : 0 < L) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ)
    (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (k : ℕ) (hk : LNatConvexOn (V L) (fbar c hh p γ μ k)) :
    LNatConvexOn (VxNeg L) (liftG (gbar c hh p γ μ k)) := by sorry

end ZipkinLostSales.LNatural

