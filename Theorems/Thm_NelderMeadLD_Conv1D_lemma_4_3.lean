import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

open Filter Topology

namespace NelderMeadLD.Conv1D

theorem lemma_4_3 (f : ℝ → ℝ) (hf : StrictConvexOn ℝ Set.univ f)
    (hlev : ∀ μ : ℝ, Bornology.IsBounded {x | f x ≤ μ})
    (xmin : ℝ) (hmin : ∀ y, f xmin ≤ f y)
    (ρ χ γ σ : ℝ) (hpar : ParamsOK ρ χ γ σ)
    (p0 : ℝ × ℝ) (h0 : IsStart f p0)
    (hρχ : 1 ≤ ρ * χ) :
    ∀ k : ℕ, Proximity ρ χ γ xmin (run f ρ χ γ σ p0 k) →
      Proximity ρ χ γ xmin (run f ρ χ γ σ p0 (k + 1)) := by sorry

end NelderMeadLD.Conv1D

