import Mathlib

namespace MassartDKW.Tight

theorem lemma_3 (δ s : ℝ) (hδ : 0 < δ) (hδs : δ < s) (hs1 : s < 1 - δ) (g : ℝ → ℝ)
    (hg : ∀ u ∈ Set.Icc (s - δ) (s + δ), 0 < g u)
    (hlog : ConvexOn ℝ (Set.Icc (s - δ) (s + δ)) (fun u => Real.log (g u))) (l : ℝ) (hl : 0 < l) :
    g s * Real.exp (-(l ^ 2) / (2 * s * (1 - s))) *
        Real.exp (-(l ^ 2 * δ ^ 2 / 6) *
          ((s * (s ^ 2 - δ ^ 2))⁻¹ + ((1 - s) * ((1 - s) ^ 2 - δ ^ 2))⁻¹)) ≤
      1 / (2 * δ) * ∫ u in (s - δ)..(s + δ), g u * Real.exp (-(l ^ 2) / (2 * u * (1 - u))) := by sorry

end MassartDKW.Tight

