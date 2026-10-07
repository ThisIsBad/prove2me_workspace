import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- Theorem 5, p. 800 (PDF 9): for `p > 0` and `c ≥ 0`, `F ∈ D_r(Π_{p,c})` iff `F` is BalkemaDeHaan.LimitTypes.tail
equivalent to a discrete distribution function `F₀` whose jumps `t₀ < t₁ < ⋯ → ∞` satisfy
(12a) and (12b). -/
theorem theorem_5 (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    InDr μ (piPC p c) ↔
      ∃ ν₀ : Measure ℝ, IsProbabilityMeasure ν₀ ∧ ∃ t : ℕ → ℝ,
        IsDiscreteWithJumps ν₀ t ∧ GapRatio t p c ∧ TailRatio ν₀ t p ∧ TailEquiv μ ν₀ := by sorry

end BalkemaDeHaan.DiscreteDomain

