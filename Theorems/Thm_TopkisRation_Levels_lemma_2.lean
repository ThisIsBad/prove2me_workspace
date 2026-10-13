import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Levels

open MeasureTheory

theorem lemma_2 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ≤ M.k) :
    (ConvexOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ)) (fun q => M.g t q.1 q.2) ∧
      ContinuousOn (fun q => M.g t q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ))) ∧
    (1 ≤ t →
      ConvexOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ)) (fun q => M.f t q.1 q.2) ∧
      ContinuousOn (fun q => M.f t q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ))) ∧
    (1 ≤ t → ∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B →
      ∃ u ∈ feasible z B, M.f t z B = M.obj t (M.g (t - 1)) z B u ∧
        ∀ u' ∈ feasible z B, M.obj t (M.g (t - 1)) z B u ≤ M.obj t (M.g (t - 1)) z B u') ∧
    (1 ≤ t → ∀ z, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b →
      Integrable (fun x => M.f t z (b + x)) (M.μ t)) := by sorry

end TopkisRation.Levels

