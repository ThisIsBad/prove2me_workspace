import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- Proof of Theorem 5, pp. 800–801 (PDF 9–10): if `F ∈ D_r(Π_{p,c})` and `F₀` is a discrete law
with jumps `t₀ < t₁ < ⋯ → ∞`, BalkemaDeHaan.LimitTypes.tail equivalent to `F`, with `R₀(t_n) = R(b_n)` for a sequence
with `R(b_{n+1})/R(b_n) → e^{-p}`, then `F₀` satisfies (12b) and its jumps satisfy (12a). -/
theorem levels_12b_12a (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : InDr μ (piPC p c))
    (b : ℕ → ℝ)
    (hb : Tendsto (fun n : ℕ => (μ (Set.Ioi (b (n + 1)))).toReal / (μ (Set.Ioi (b n))).toReal)
      atTop (𝓝 (Real.exp (-p))))
    (ν₀ : Measure ℝ) [IsProbabilityMeasure ν₀] (t : ℕ → ℝ)
    (hν₀ : IsDiscreteWithJumps ν₀ t) (hlev : ∀ n, ν₀ (Set.Ioi (t n)) = μ (Set.Ioi (b n)))
    (heq : TailEquiv μ ν₀) :
    TailRatio ν₀ t p ∧ GapRatio t p c := by sorry

end BalkemaDeHaan.DiscreteDomain

