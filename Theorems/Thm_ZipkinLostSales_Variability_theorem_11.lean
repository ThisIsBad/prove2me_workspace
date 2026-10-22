import Mathlib
import Definitions.Def_ZipkinLostSales_Variability_Model
import Definitions.Def_StochasticOrders_Convex_ConvexOrder
open MeasureTheory

namespace ZipkinLostSales.Variability

/-- Theorem 11 (Zipkin 2008, p. 941): if the demand `d(φ)`, with law `μ φ`, is increasing in
`φ` with respect to the convex order, then the optimal cost `f̄_t(v; φ)` is nondecreasing in `φ`
for all `t`, i.e. for every number of periods to go `k` and every state `v ∈ ZipkinLostSales.LNatural.V`. -/
theorem theorem_11 {L : ℕ} (hL : 0 < L) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (μ : ℝ → Measure ℝ)
    (hμprob : ∀ φ, IsProbabilityMeasure (μ φ)) (hμnonneg : ∀ φ, μ φ (Set.Iio 0) = 0)
    (hμint : ∀ φ, Integrable id (μ φ))
    (hcx : ∀ φ φ' : ℝ, φ ≤ φ' → StochasticOrders.Convex.ConvexOrder (μ φ) (μ φ') id id) :
    ∀ k : ℕ, ∀ v ∈ ZipkinLostSales.LNatural.V L, Monotone (fun φ : ℝ => ZipkinLostSales.LNatural.fbar c hh p γ (μ φ) k v) := by sorry

end ZipkinLostSales.Variability

