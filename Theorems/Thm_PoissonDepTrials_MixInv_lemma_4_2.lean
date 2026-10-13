import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (r s k m : ℕ) (hm : 1 ≤ m)
    (Y : Ω → (Fin r → ℝ)) (hY : Measurable[sigmaIcc X 1 k] Y)
    (Z : Ω → (Fin s → ℝ)) (hZ : Measurable[sigmaIci X (k + m)] Z)
    (f : (Fin r → ℝ) × (Fin s → ℝ) → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    ∀ᵐ ω ∂P, |(P[fun ω => f (Y ω, Z ω) | MeasurableSpace.comap Y inferInstance]) ω
      - ∫ z, f (Y ω, z) ∂(P.map Z)| ≤ 2 * M * φ m := by sorry

end PoissonDepTrials.MixInv

