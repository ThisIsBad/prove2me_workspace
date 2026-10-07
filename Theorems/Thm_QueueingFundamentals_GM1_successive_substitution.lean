import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory Filter Topology

/-- Eq. (5.59): when `λ/μ < 1`, successive substitution `z^{(k+1)} = β(z^{(k)})` started at any
`0 < z^{(0)} < 1` converges to the root `r_0 ∈ (0, 1)` of `z = β(z)`. -/
theorem successive_substitution (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1)
    (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0 : ℝ) 1) (hroot : beta A mu (r0 : ℂ) = (r0 : ℂ))
    (z0 : ℝ) (hz0 : z0 ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun k : ℕ => (fun x : ℝ => (beta A mu (x : ℂ)).re)^[k] z0) atTop (𝓝 r0) := by sorry

end QueueingFundamentals.GM1

