import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem theorem_5_1 (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) (χ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK 1 χ (1 / 2) σ)
    (Δ : ℕ → Fin 3 → E 2) (hrun : IsNMRun f 1 χ (1 / 2) σ Δ) (hnd : Nondegenerate (Δ 0)) :
    ∃ L : ℝ, ∀ i : Fin 3, Tendsto (fun k => f (Δ k i)) atTop (𝓝 L) := by sorry

end NelderMeadLD.Dim2

