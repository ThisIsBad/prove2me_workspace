import Mathlib
import Definitions.Def_DeterioratingJobs_Weighted_Model

namespace DeterioratingJobs.Weighted

open MeasureTheory

/-- Proposition 2, p. 497: identity order minimizes expected weighted completion cost. -/
theorem proposition2 {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (hX : ∀ i, Integrable (X i) P)
    (hX0 : ∀ i ω, 0 ≤ X i ω)
    (hα : ∀ i, 0 < α i) (hc : ∀ i, 0 < c i)
    (hindex : StrictMono (fun i : Fin N => (∫ ω, X i ω ∂P) / α i))
    (hcost : StrictMono (fun i : Fin N => α i / (c i * (1 + α i)))) :
    ∀ σ : Equiv.Perm (Fin N),
      (∫ ω, totalCost X α c 1 ω ∂P) ≤
        ∫ ω, totalCost X α c σ ω ∂P := by sorry

end DeterioratingJobs.Weighted

