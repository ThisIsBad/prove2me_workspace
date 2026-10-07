import Mathlib
import Definitions.Def_DeterioratingJobs_Makespan_InterchangeSum
import Definitions.Def_DeterioratingJobs_Makespan_Model

namespace DeterioratingJobs.Makespan

open MeasureTheory

/-- Section 1, after Eq. (2) (Browne–Yechiali 1990, p. 496): the expected makespan has the form (1)
of Lemma 1 with `μ_i = E(X_i)` and `γ_i = 1 + α_i`:
`E S_N(π) = ∑_i E(X_{π(i)}) ∏_{r>i} (1 + α_{π(r)})`. -/
theorem expected_makespan_eq_lemma1Sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → ℝ) (hX : ∀ i, Integrable (X i) P)
    (α : Fin N → ℝ) (π : Equiv.Perm (Fin N)) :
    expectedMakespan P X α π =
      lemma1Sum (fun i => ∫ ω, X i ω ∂P) (fun i => 1 + α i) π := by sorry

end DeterioratingJobs.Makespan

