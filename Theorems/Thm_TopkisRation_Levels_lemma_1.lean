import Mathlib

namespace TopkisRation.Levels

theorem lemma_1 {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (A : Set (E × F)) (hA : Convex ℝ A) (φ : E × F → ℝ) (hφ : ConvexOn ℝ A φ)
    (hbdd : ∀ u, BddBelow (φ '' {q | q ∈ A ∧ q.1 = u})) :
    ConvexOn ℝ (Prod.fst '' A) (fun u => sInf (φ '' {q | q ∈ A ∧ q.1 = u})) := by sorry

end TopkisRation.Levels

