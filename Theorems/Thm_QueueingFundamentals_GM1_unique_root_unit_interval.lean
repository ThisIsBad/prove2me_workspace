import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- pp.261–262, the graphs of (5.58): `z = β(z)` has at most one root in `(0, 1)`, and it has one
exactly when `λ/μ < 1`. -/
theorem unique_root_unit_interval (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) :
    (∀ r s : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 → beta A mu (r : ℂ) = (r : ℂ) →
        s ∈ Set.Ioo (0 : ℝ) 1 → beta A mu (s : ℂ) = (s : ℂ) → r = s) ∧
      ((∃ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 ∧ beta A mu (r : ℂ) = (r : ℂ)) ↔ lam / mu < 1) := by sorry

end QueueingFundamentals.GM1

