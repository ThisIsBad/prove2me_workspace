import Mathlib.Probability.Kernel.Invariance
import Definitions.Def_SmithHitAndRun_SymMixing_uniformLaw
import Definitions.Def_SmithHitAndRun_SymMixing_IsSymmetricMixingKernel

open MeasureTheory ProbabilityTheory Filter


namespace SmithHitAndRun.SymMixing

theorem lemma1_core {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) :
    ∀ A : Set α, MeasurableSet A →
      uniformLaw V A = ∫⁻ x, P x A ∂(uniformLaw V) := by
  obtain ⟨hf, hP, hsym⟩ := h
  intro A hA
  unfold uniformLaw
  simp only [Measure.smul_apply, smul_eq_mul, lintegral_smul_measure]
  congr 1
  have h1 : ∀ y, ∫⁻ x, f y x ∂V = 1 := by
    intro y
    have := hP y Set.univ MeasurableSet.univ
    rw [measure_univ, Measure.restrict_univ] at this
    exact (lintegral_congr (fun x => hsym x y)).trans this.symm
  calc V A = ∫⁻ y in A, 1 ∂V := by simp
    _ = ∫⁻ y in A, ∫⁻ x, f y x ∂V ∂V := by simp_rw [h1]
    _ = ∫⁻ x, ∫⁻ y in A, f y x ∂V ∂V := by
        symm
        exact lintegral_lintegral_swap (hf.comp measurable_swap).aemeasurable
    _ = ∫⁻ x, P x A ∂V := by
        refine lintegral_congr (fun x => ?_)
        rw [hP x A hA]

end SmithHitAndRun.SymMixing

open SmithHitAndRun.SymMixing


theorem solution {α : Type*} [MeasurableSpace α]
    (V : Measure α) [IsFiniteMeasure V] (hV : V ≠ 0)
    (P : Kernel α α) [IsMarkovKernel P] (f : α → α → ENNReal)
    (h : IsSymmetricMixingKernel V P f) :
    ∀ A : Set α, MeasurableSet A →
      uniformLaw V A = ∫⁻ x, P x A ∂(uniformLaw V) := by
  exact lemma1_core V hV P f h
