import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- §3, p. 800 (PDF 9): if `F₁` is BalkemaDeHaan.LimitTypes.tail equivalent to `F₂ ∈ D_r(Π_{p,c})`, then
`F₁ ∈ D_r(Π_{p,c})`. -/
theorem tailEquiv_mem_Dr (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h12 : TailEquiv μ₁ μ₂) (h2 : InDr μ₂ (piPC p c)) :
    InDr μ₁ (piPC p c) := by sorry

end BalkemaDeHaan.DiscreteDomain

