import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model

namespace GilmoreGomoryTSP.Bottleneck

theorem psiPrime_minimizes_bottleneck {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ))
    (T : Finset (Fin n)) (hT : IsMinSpanningTree f g A B φ T) :
    GilmoreGomoryTSP.MinCost.IsTour (psiPrime φ T) ∧
      ∀ ψ : Equiv.Perm (Fin (n + 1)), GilmoreGomoryTSP.MinCost.IsTour ψ → m f g A B (psiPrime φ T) ≤ m f g A B ψ := by sorry

end GilmoreGomoryTSP.Bottleneck

