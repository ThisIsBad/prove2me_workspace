import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run

namespace GPSAnalysis.Core

/-- Lemma 3.3 (Audet–Dennis 2003, p. 895). Under A1 and A3 there is a positive integer `r⁺`
with `Δ_k ≤ Δ_0 τ^{r⁺}` for every `k ≥ 0`. -/
theorem mesh_size_bounded {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) (hA3 : AssumptionA3 R) :
    ∃ r : ℕ, 0 < r ∧ ∀ k, R.Δ k ≤ R.Δ 0 * (P.τ : ℝ) ^ r := by sorry

end GPSAnalysis.Core
