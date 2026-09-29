import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run

open Filter Topology

namespace GPSAnalysis.Core

/-- Theorem 3.1 (Audet–Dennis 2003, p. 894). Under A1 and A3 the iterate sequence has a limit
point; if `f` is lower semicontinuous at a limit point `x̄`, then `lim_k f(x_k)` exists (finite)
and is `≥ f(x̄)`; if `f` is continuous at every limit point, all limit points have the same value. -/
theorem limit_point_properties {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) (hA3 : AssumptionA3 R) :
    (∃ xbar : Fin n → ℝ, MapClusterPt xbar atTop R.x) ∧
    (∀ xbar : Fin n → ℝ, MapClusterPt xbar atTop R.x → LowerSemicontinuousAt P.f xbar →
      ∃ ℓ : ℝ, Tendsto (fun k => P.f (R.x k)) atTop (𝓝 (ℓ : WithTop ℝ)) ∧
        P.f xbar ≤ (ℓ : WithTop ℝ)) ∧
    ((∀ xbar : Fin n → ℝ, MapClusterPt xbar atTop R.x → ContinuousAt P.f xbar) →
      ∀ x₁ x₂ : Fin n → ℝ, MapClusterPt x₁ atTop R.x → MapClusterPt x₂ atTop R.x →
        P.f x₁ = P.f x₂) := by sorry

end GPSAnalysis.Core
