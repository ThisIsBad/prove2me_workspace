import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- Equations (4) and (5), printed p. 4. -/
theorem equations_4_5 {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (x s dx ds : Fin n → ℝ)
    (dy : Fin m → ℝ) (γ θ : ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (hd : SearchDirection A x s γ dx dy ds) :
    mu (stepX x dx θ) (stepS s ds θ) =
      (1 - θ) * mu x s + θ * γ * mu x s ∧
    (fun j => stepX x dx θ j * stepS s ds θ j -
      mu (stepX x dx θ) (stepS s ds θ)) =
      (fun j => (1 - θ) * (x j * s j - mu x s) + θ ^ 2 * (dx j * ds j)) := by sorry

end AdaptiveStepIPM.PredCorr

