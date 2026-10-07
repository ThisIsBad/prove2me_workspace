import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- p.262 (Rouché's theorem): when `λ/μ < 1` there is exactly one complex root of `z = β(z)` with
`|z| < 1`. -/
theorem unique_root_unit_disk (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1) :
    ∃! z : ℂ, ‖z‖ < 1 ∧ beta A mu z = z := by sorry

end QueueingFundamentals.GM1

