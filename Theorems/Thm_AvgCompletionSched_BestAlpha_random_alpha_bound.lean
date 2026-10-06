import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem random_alpha_bound {n : ℕ} {I : Instance n} (P : PreemptiveSchedule I)
    (f : ℝ → ℝ) (hf_nonneg : ∀ α ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ f α)
    (hf_int : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hf_one : ∫ α in (0 : ℝ)..1, f α = 1)
    (δ : ℝ) (hδ : ∀ β ∈ Set.Ioc (0 : ℝ) 1, ∫ α in (0 : ℝ)..β, (1 + α - β) / β * f α ≤ δ) :
    (∀ i, IntervalIntegrable (fun α => f α * P.Calpha α i) MeasureTheory.volume 0 1 ∧
        ∫ α in (0 : ℝ)..1, f α * P.Calpha α i ≤ (1 + δ) * P.CP i) ∧
      ∫ α in (0 : ℝ)..1, f α * ∑ i, P.Calpha α i ≤ (1 + δ) * ∑ i, P.CP i := by sorry
end AvgCompletionSched.BestAlpha

