import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Theorem 4 (Karlin and Scarf 1958 and Morton 1969; Zipkin 2008, p. 939): for all `t`, the
functions `f̄_t(v)` and `ḡ_t(v, ζ)` are L♮-convex. With `k` the number of periods to go,
`fbar … k` is L♮-convex on `V` and `gbar … k` is L♮-convex on `V × ℜ⁻`, for every `k`. -/
theorem theorem_4 (L : ℕ) (hL : 0 < L) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ)
    (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (k : ℕ) :
    LNatConvexOn (V L) (fbar c hh p γ μ k) ∧
      LNatConvexOn (VxNeg L) (liftG (gbar c hh p γ μ k)) := by sorry

end ZipkinLostSales.LNatural

