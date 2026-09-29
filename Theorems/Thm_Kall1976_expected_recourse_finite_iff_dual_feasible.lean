import Definitions.Def_Kall1976_RecourseDifferentiability
import Definitions.Def_KallMayer_Recourse_CompleteRecourse

open MeasureTheory

namespace Kall1976

/-- Kall (1976), III.15, printed54/PDF60, with the four moment alternatives
of III.10–11 (printed46–48). Complete recourse makes every right-hand side
feasible; finite expected cost is equivalent to almost-sure dual feasibility.
The data law formulation retains arbitrary joint distributions of (A,b,q).
Finiteness is existence of a real value of the signed extended expectation,
not of its totalized real projection. No finiteness premise is inherited from
III.10: III.15 cites only its integrability conditions. The source fixes any x.
All definitions are reused unchanged; no auxiliary theorem is introduced. -/
theorem expected_recourse_finite_iff_dual_feasible
    {m n p : ℕ} (μ : Measure (RecourseData m n p)) [IsProbabilityMeasure μ]
    (W : Matrix (Fin m) (Fin p) ℝ)
    (hcomplete : KallMayer.Recourse.CompleteRecourse W)
    (hmoments : recourseMomentAlternative μ)
    (x : Fin n → ℝ) :
    (∃ v : ℝ, extendedExpectedRecourse μ W x = (v : EReal)) ↔
      (∀ᵐ d ∂μ, ∃ z : Fin m → ℝ,
        ∀ j : Fin p, Matrix.mulVec W.transpose z j ≤ d.2.2 j) := by sorry

end Kall1976
