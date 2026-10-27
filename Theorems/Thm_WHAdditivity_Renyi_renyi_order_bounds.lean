import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem renyi_order_bounds {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ)
    (hρ : IsDensity ρ) (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    renyiEntropy 2 ρ ≤ renyiEntropy p ρ ∧ renyiEntropy p ρ ≤ vonNeumannEntropy ρ := by sorry

end WHAdditivity.Renyi

