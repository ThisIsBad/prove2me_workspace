import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Proof of Theorem 4 (Zipkin 2008, p. 939): in program (3)/(4) with continuation `f̄_{t+1}`
(here `fbar … k`), filling as much demand as possible (`a = min{d, v₀ − v₁}`, i.e.
`v₊ = max(v₀ − d, v₁)`) is optimal, so `κ̄(v, ζ | d) = q̂(v₀ − v₁ − d) + γ f̄_{t+1}(v₊)` with `v₊`
the transition of p. 938. -/
theorem optimal_fill (L : ℕ) (hL : 0 < L) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ)
    (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (k : ℕ) (v : Fin L → ℝ) (hv : v ∈ V L) (ζ : ℝ) (hζ : ζ ≤ 0) (d : ℝ) (hd : 0 ≤ d) :
    kappa hh p γ (fbar c hh p γ μ k) d v ζ =
      qhat hh p (vext v 0 - vext v 1 - d) + γ * fbar c hh p γ μ k (next v d ζ) := by sorry

end ZipkinLostSales.LNatural

