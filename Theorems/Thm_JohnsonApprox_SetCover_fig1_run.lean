import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_C1
import Definitions.Def_JohnsonApprox_SetCover_Fig1

namespace JohnsonApprox.SetCover

theorem fig1_run (k : ℕ) (hk : 1 ≤ k) :
    InSC k (fig1 k) ∧ fig1F₀ k ∈ subcovers (fig1 k) ∧ opt (fig1 k) = k.factorial ∧
      Choosable (fig1 k) (fig1F₁ k) ∧
      ((fig1F₁ k).card : ℚ) = k.factorial * harmonic k := by sorry

end JohnsonApprox.SetCover

