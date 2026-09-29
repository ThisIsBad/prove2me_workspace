import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game

open Filter Topology

namespace CalibratedCE.Generic

theorem exists_play_with_limit {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD : IsJointDist D) :
    ∃ (x : ℕ → Fin m) (y : ℕ → Fin n), (∀ t, 0 < D (x t) (y t)) ∧
      ∀ a b, Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b)) := by sorry

end CalibratedCE.Generic
