import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- §3, p. 800 (PDF 9): a discrete law whose jumps `t₀ < t₁ < ⋯ → ∞` satisfy (12a) and (12b)
lies in the domain of residual life time attraction of `Π_{p,c}`. -/
theorem discrete_mem_Dr (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℕ → ℝ)
    (hν : IsDiscreteWithJumps ν t) (h12a : GapRatio t p c) (h12b : TailRatio ν t p) :
    InDr ν (piPC p c) := by sorry

end BalkemaDeHaan.DiscreteDomain

