import Mathlib
import Definitions.Def_ZipkinLostSales_Variability_Model
open MeasureTheory

namespace ZipkinLostSales.Variability

/-- Proof of Theorem 4 (Zipkin 2008, p. 939): in program (3)/(4) with continuation `f̄_{t+1}` the
optimal sales are `a = min{d, v₀ − v₁}`, so that `κ̄(v, ζ | d) = q̂(v₀ − v₁ − d) + γ f̄_{t+1}(v₊)`
with `v₊` the transition of p. 938. Stated for one demand law `μ` and every number of periods
to go `k`. -/
theorem kappa_fbar_eq {L : ℕ} (hL : 0 < L) (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh)
    (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ) :
    ∀ k : ℕ, ∀ v ∈ ZipkinLostSales.LNatural.V L, ∀ ζ : ℝ, ζ ≤ 0 → ∀ d : ℝ, 0 ≤ d →
      ZipkinLostSales.LNatural.kappa hh p γ (ZipkinLostSales.LNatural.fbar c hh p γ μ k) d v ζ
        = ZipkinLostSales.LNatural.qhat hh p (ZipkinLostSales.LNatural.vext v 0 - ZipkinLostSales.LNatural.vext v 1 - d) + γ * ZipkinLostSales.LNatural.fbar c hh p γ μ k (ZipkinLostSales.LNatural.next v d ζ) := by sorry

end ZipkinLostSales.Variability

