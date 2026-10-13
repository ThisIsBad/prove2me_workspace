import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_4_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (m : ℕ) (hm : 1 ≤ m) (a b c d e e' : ℕ) (ha : 1 ≤ a) (hbc : b + m ≤ c) (hde : d + m ≤ e)
    (Y T Z : Ω → ℝ) (hY : Measurable[sigmaIcc X a b] Y) (hT : Measurable[sigmaIcc X c d] T)
    (hZ : Measurable[sigmaIcc X e e'] Z)
    (g : ℝ → ℝ) (hg : Measurable g) (Mg : ℝ) (hMg : ∀ x, |g x| ≤ Mg)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) (Mf : ℝ) (hMf : ∀ x, |f x| ≤ Mf) :
    |∫ ω, f (Y ω, Z ω) * g (T ω) ∂P - (∫ ω, f (Y ω, Z ω) ∂P) * ∫ ω, g (T ω) ∂P|
      ≤ 4 * φ m * Mf * ∫ ω, |g (T ω)| ∂P
        + 2 * φ m * Mg * ∫ x, |f x| ∂((P.map Y).prod (P.map Z)) := by sorry

end PoissonDepTrials.MixInv

