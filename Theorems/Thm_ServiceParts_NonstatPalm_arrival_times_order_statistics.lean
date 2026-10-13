import Mathlib
import Definitions.Def_ServiceParts_NonstatPalm_ResupplySystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.NonstatPalm

theorem arrival_times_order_statistics {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (S : ResupplySystem Ω P E)
    {t : ℝ} (hm : 0 < S.meanFn t) (n : ℕ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ (Set.Iic x) = ENNReal.ofReal (S.arrivalCdf t x))
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    P ({ω | S.demandCount t ω = n} ∩ {ω | (fun i : Fin n => S.epoch (i : ℕ) ω) ∈ A}) =
      P {ω | S.demandCount t ω = n} *
        Measure.pi (fun _ : Fin n => μ) {x : Fin n → ℝ | x ∘ Tuple.sort x ∈ A} := by sorry

end ServiceParts.NonstatPalm

