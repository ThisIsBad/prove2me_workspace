import Mathlib
import Definitions.Def_DeterioratingJobs_Makespan_Model

namespace DeterioratingJobs.Makespan

open MeasureTheory

/-- Browne–Yechiali 1990, p. 496, Section 1, the sentence after Eq. (2): with growth rates
`α_i > 0`, any schedule `π` that processes the jobs by increasing `E(X_i)/α_i` minimizes the
expected makespan `E S_N` over all schedules. -/
theorem expected_makespan_index_rule {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → ℝ) (hX : ∀ i, Integrable (X i) P)
    (α : Fin N → ℝ) (hα : ∀ i, 0 < α i) (π : Equiv.Perm (Fin N))
    (hπ : Monotone (fun k : Fin N => (∫ ω, X (π k) ω ∂P) / α (π k))) :
    ∀ σ : Equiv.Perm (Fin N), expectedMakespan P X α π ≤ expectedMakespan P X α σ := by sorry

end DeterioratingJobs.Makespan

