import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model

namespace GilmoreGomoryTSP.Bottleneck

theorem phi_minimizes_m {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) :
    ∀ ψ : Equiv.Perm (Fin (n + 1)), m f g A B φ ≤ m f g A B ψ := by sorry

end GilmoreGomoryTSP.Bottleneck

