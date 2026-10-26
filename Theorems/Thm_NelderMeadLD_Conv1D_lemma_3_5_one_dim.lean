import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem lemma_3_5_one_dim (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0) :
    ∀ k : ℕ, move f ρ χ γ (run f ρ χ γ σ p0 k) ≠ Move.shrink := by sorry

end NelderMeadLD.Conv1D

