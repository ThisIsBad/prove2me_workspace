import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

end MonotonicSolutions.StrongMono

open MonotonicSolutions.StrongMono

theorem solution {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hφ : IsStronglyMonotonic φ) : IsMarginal φ := by
  intro v w i h
  exact le_antisymm (hφ w v i (fun S => (h S).le)) (hφ v w i (fun S => (h S).ge))
