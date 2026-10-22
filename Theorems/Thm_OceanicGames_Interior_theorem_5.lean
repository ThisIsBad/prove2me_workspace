import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- Theorem 5, (5.4), p. 18: if `Γ = [c; w_1, …, w_m; α]` and `Γ⁺ = [d; w_1, …, w_{m+1}; α]` are
both interior, then `φ⁺_{m+1} = (1/α) Φ w_{m+1}`. -/
theorem theorem_5 {m : ℕ} (c d α w' : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (hw' : 0 ≤ w') (hΓ : IsInterior c α w) (hΓ' : IsInterior d α (addWeight w w')) :
    value d α (addWeight w w') (Fin.last m) = 1 / α * oceanValue c α w * w' := by sorry

end OceanicGames.Interior

