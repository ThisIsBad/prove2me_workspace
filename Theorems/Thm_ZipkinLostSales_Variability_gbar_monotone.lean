import Mathlib
import Definitions.Def_ZipkinLostSales_Variability_Model
import Definitions.Def_StochasticOrders_Convex_ConvexOrder
open MeasureTheory

namespace ZipkinLostSales.Variability

/-- Proof of Theorem 11 (Zipkin 2008, p. 941), the induction step: if the demand `d(φ)` with law
`μ φ` increases in `φ` in the convex order and `f̄_{t+1}(v; φ)` is nondecreasing in `φ` on `V`,
then `ḡ_t(v, ζ; φ)` is nondecreasing in `φ` for every `v ∈ ZipkinLostSales.LNatural.V` and `ζ ≤ 0`. Time is indexed by
the number of periods to go `k` (`gbar … k` has continuation `fbar … k`). -/
theorem gbar_monotone {L : ℕ} (hL : 0 < L) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (μ : ℝ → Measure ℝ)
    (hμprob : ∀ φ, IsProbabilityMeasure (μ φ)) (hμnonneg : ∀ φ, μ φ (Set.Iio 0) = 0)
    (hμint : ∀ φ, Integrable id (μ φ))
    (hcx : ∀ φ φ' : ℝ, φ ≤ φ' → StochasticOrders.Convex.ConvexOrder (μ φ) (μ φ') id id) :
    ∀ k : ℕ, (∀ v ∈ ZipkinLostSales.LNatural.V L, Monotone (fun φ : ℝ => ZipkinLostSales.LNatural.fbar c hh p γ (μ φ) k v)) →
      ∀ v ∈ ZipkinLostSales.LNatural.V L, ∀ ζ : ℝ, ζ ≤ 0 → Monotone (fun φ : ℝ => ZipkinLostSales.LNatural.gbar c hh p γ (μ φ) k v ζ) := by sorry

end ZipkinLostSales.Variability

