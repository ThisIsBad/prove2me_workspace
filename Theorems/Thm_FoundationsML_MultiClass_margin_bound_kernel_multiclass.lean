import Mathlib
import Definitions.Def_FoundationsML_MultiClass_GeneralizationError
import Definitions.Def_FoundationsML_MultiClass_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_MultiClass_IsPDS
import Definitions.Def_FoundationsML_MultiClass_KernelHypothesisClass

open MeasureTheory

namespace FoundationsML.MultiClass

/-- Corollary 9.4 (Margin bound for multi-class classification with kernel-based hypotheses;
Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
p. 220, PDF p. 237). Under Proposition 9.3's hypotheses on `K`, `Φ`, `r`, fix `ρ > 0`. Then,
for any `δ > 0`, with probability at least `1 − δ`, the following holds for all
`h ∈ H_{K,p}`: `R(h) ≤ R̂_{S,ρ}(h) + 4k sqrt(r²Λ²/ρ²/m) + sqrt(log(1/δ)/(2m))`. -/
theorem margin_bound_kernel_multiclass
    {X Hb : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (K : X → X → ℝ) (Φ : X → Hb) (hK : IsPDS K) (hΦ : ∀ x y, K x y = (inner (𝕜 := ℝ) (Φ x) (Φ y) : ℝ))
    (r : ℝ) (hr : 0 < r) (hrK : ∀ x, K x x ≤ r ^ 2)
    (k : ℕ) (hk2 : 2 ≤ k) (p Λ : ℝ) (hp : 1 ≤ p) (hΛ : 0 < Λ)
    (f : X → Fin k) (m : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ KernelHypothesisClass Φ k p Λ, GeneralizationError D f h ≤
        EmpiricalMarginLoss ρ S f h + 4 * (k : ℝ) * Real.sqrt (r ^ 2 * Λ ^ 2 / ρ ^ 2 / m) +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.MultiClass
