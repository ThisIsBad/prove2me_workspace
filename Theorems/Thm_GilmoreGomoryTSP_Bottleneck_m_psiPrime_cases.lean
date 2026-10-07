import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model

namespace GilmoreGomoryTSP.Bottleneck

theorem m_psiPrime_cases {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ))
    (T : Finset (Fin n)) (hT : IsMinSpanningTree f g A B φ T) :
    (∃ j : Fin (n + 1), m f g A B (psiPrime φ T) = GilmoreGomoryTSP.MinCost.c f g A B j (φ j)) ∨
      ∃ q ∈ T, m f g A B (psiPrime φ T) = arcCost f g A B φ q := by sorry

end GilmoreGomoryTSP.Bottleneck

