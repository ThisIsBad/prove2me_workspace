import Definitions.Def_LeastSquaresTD_Absorbing_Estimator

namespace LeastSquaresTD.Absorbing

open MeasureTheory Filter Topology

/-- Proof of Theorem 1, p. 44, first two sentences. The paper calls `π x` the
expected number of departures from `x` per trial. With `n` indexing restart
steps, the limit here differs by one common positive time-scale factor;
the expression in Lemma 5 is invariant under that factor. -/
theorem visit_frequencies
    {X Ω : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Chain X) (S : X → ℝ) (Z : ℕ → Ω → X)
    (habs : C.IsAbsorbing) (hS_nonneg : ∀ x, 0 ≤ S x)
    (hS_sum : ∑ x, S x = 1) (haccess : C.AllAccessible S)
    (hlaw : HasRestartLaw C S μ Z) :
    ∃ π : X → ℝ,
      (∀ x : C.Nonabsorbing, 0 < π x.val) ∧
      (∀ x, C.P x x = 1 → π x = 0) ∧
      (∀ᵐ ω ∂μ, (∀ (x : X) (N : ℕ), ∃ n ≥ N, Z n ω = x) ∧
        (∀ x, Tendsto (fun n => outFrequency C (fun k => Z k ω) x n)
          atTop (𝓝 (π x)))) := by sorry

end LeastSquaresTD.Absorbing

