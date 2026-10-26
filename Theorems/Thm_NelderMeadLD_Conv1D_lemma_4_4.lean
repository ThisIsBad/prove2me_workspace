import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem lemma_4_4 (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0) :
    ∃ L : ℝ, Tendsto (fun k => f (run f ρ χ γ σ p0 k).1) atTop (𝓝 L) ∧
      Tendsto (fun k => f (run f ρ χ γ σ p0 k).2) atTop (𝓝 L) := by sorry

end NelderMeadLD.Conv1D

