import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem renyi_tensor_additive (N : ℕ) (d : Fin N → ℕ)
    (ρ : (j : Fin N) → Matrix (Fin (d j)) (Fin (d j)) ℂ) (hρ : ∀ j, IsDensity (ρ j))
    (p : ℝ) (hp : 1 ≤ p) :
    renyiEntropy p (tensorMatrix d ρ) = ∑ j, renyiEntropy p (ρ j) := by sorry

end WHAdditivity.Renyi

