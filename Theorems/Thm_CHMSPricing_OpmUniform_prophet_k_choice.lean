import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_Prophet

namespace CHMSPricing.OpmUniform

open MeasureTheory ProbabilityTheory

theorem prophet_k_choice {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω) (hXint : ∀ i, Integrable (X i) P) (a b c : ℝ)
    (ha : a = ∑ i : Fin k, ∫ ω, max 0 (orderStat (fun j => X j ω) i - a / k) ∂P)
    (hb : b = ∑ i, ∫ ω, max 0 (X i ω - b / k) ∂P)
    (hac : a ≤ k * c) (hcb : k * c ≤ b) :
    ∑ i : Fin k, ∫ ω, orderStat (fun j => X j ω) i ∂P ≤
      2 * ∑ i : Fin k, ∫ ω, X (threshIdx hkn (fun j => X j ω) c i) ω ∂P := by sorry

end CHMSPricing.OpmUniform

