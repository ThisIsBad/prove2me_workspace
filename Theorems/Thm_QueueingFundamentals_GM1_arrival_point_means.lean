import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- Eq. (5.61): at arrival points, the mean number in the system is `L^{(A)} = r_0/(1 - r_0)` and the
mean number in queue is `L_q^{(A)} = r_0^2/(1 - r_0)`. -/
theorem arrival_point_means (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1)
    (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0 : ℝ) 1) (hroot : beta A mu (r0 : ℂ) = (r0 : ℂ))
    (q : ℕ → ℝ) (hq : IsArrivalPointStationary A mu q) :
    HasSum (fun n : ℕ => (n : ℝ) * q n) (r0 / (1 - r0)) ∧
      HasSum (fun n : ℕ => (n : ℝ) * q (n + 1)) (r0 ^ 2 / (1 - r0)) := by sorry

end QueueingFundamentals.GM1

