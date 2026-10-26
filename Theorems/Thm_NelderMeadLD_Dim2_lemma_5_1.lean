import Mathlib
import Definitions.Def_NelderMeadLD_Dim2_Algorithm
open Filter Topology

namespace NelderMeadLD.Dim2

theorem lemma_5_1 (f : E 2 → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ}) (χ σ : ℝ) (hpar : NelderMeadLD.Conv1D.ParamsOK 1 χ (1 / 2) σ)
    (Δ : ℕ → Fin 3 → E 2) (hrun : IsNMRun f 1 χ (1 / 2) σ Δ) (hnd : Nondegenerate (Δ 0))
    (hconst : ∀ k, Δ k 0 = Δ 0 0) :
    ∀ i, Tendsto (fun k => Δ k i) atTop (𝓝 (Δ 0 0)) := by sorry

end NelderMeadLD.Dim2

