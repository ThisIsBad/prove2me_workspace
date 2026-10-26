import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem eq_4_9 (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ) (xmin : ℝ) :
    ∀ p : ℝ × ℝ, Proximity ρ χ γ xmin p → |xmin - p.1| ≤ NNM ρ χ γ * diam p := by sorry

end NelderMeadLD.Conv1D

