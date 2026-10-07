import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- Eq. (5.60) with the root result of pp.261–262: when `ρ = λ/μ < 1` there is a root `r_0 ∈ (0, 1)`
of `z = β(z)`, it is the only root of `z = β(z)` in the open unit disk, the geometric vector
`q_n = (1 - r_0) r_0^n` solves `qP = q`, `qe = 1`, and it is the only probability vector that does. -/
theorem arrival_point_geometric (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1) :
    ∃ r0 : ℝ, r0 ∈ Set.Ioo (0 : ℝ) 1 ∧ beta A mu (r0 : ℂ) = (r0 : ℂ) ∧
      (∀ z : ℂ, ‖z‖ < 1 → beta A mu z = z → z = (r0 : ℂ)) ∧
      IsArrivalPointStationary A mu (fun n => (1 - r0) * r0 ^ n) ∧
      ∀ q : ℕ → ℝ, IsArrivalPointStationary A mu q → q = fun n => (1 - r0) * r0 ^ n := by sorry

end QueueingFundamentals.GM1

