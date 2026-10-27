import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory

namespace FragLOB.Collapse

theorem proof_thm1_separable {N : ℕ} (M : Market N) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Set.Iio 0) = 0) (hmean : Integrable (fun γ => γ) F) (d : Fin N → ℝ)
    (pi : ℝ → Fin (N + 1) → ℝ) (hpi : IsRouting pi) :
    (∀ pi' : ℝ → Fin (N + 1) → ℝ, IsRouting pi' →
        ∫ γ, payoff M d γ (pi' γ) ∂F ≤ ∫ γ, payoff M d γ (pi γ) ∂F) ↔
      ∀ᵐ γ ∂F, IsBestResponse M d γ (pi γ) := by sorry

end FragLOB.Collapse

