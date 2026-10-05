import Mathlib

namespace EkelandVP.General

theorem ekeland_variational_principle {V : Type*} [MetricSpace V] [CompleteSpace V]
    (F : V → EReal) (hF : LowerSemicontinuous F) (hne : ∃ v₀ : V, F v₀ ≠ ⊤)
    (hbdd : ⊥ < ⨅ v, F v) (ε : ℝ) (hε : 0 < ε) (u : V)
    (hu : F u ≤ (⨅ v, F v) + (ε : EReal)) (lam : ℝ) (hlam : 0 < lam) :
    ∃ v : V, F v ≤ F u ∧ dist u v ≤ lam ∧
      ∀ w : V, w ≠ v → F v - ((ε / lam * dist v w : ℝ) : EReal) < F w := by sorry

end EkelandVP.General

