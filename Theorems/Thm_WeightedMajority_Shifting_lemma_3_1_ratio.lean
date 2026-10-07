import Mathlib
import Definitions.Def_WeightedMajority_Shifting_WML

namespace WeightedMajority.Shifting

theorem lemma_3_1_ratio {n T : ℕ} {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1 / 2)
    (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool)
    (hrun : IsWMLRun β γ x ρ w lam) (t : Fin T) (hmis : lam t ≠ ρ t) :
    totalWeight (w ((t : ℕ) + 1)) ≤ uFactor β γ * totalWeight (w t) := by sorry

end WeightedMajority.Shifting

