import Mathlib

namespace KallenbergLP.SemiMarkov

open MeasureTheory

/-- The finite semi-Markov decision model of Chapter 7, before a reward criterion is chosen.
Actions can depend on the current state. The holding-time law is conditional on both the
chosen action and the next state and may have an atom at zero. -/
structure Model (S U : Type*) [Fintype S] [Nonempty S] [Fintype U] where
  actions : S → Finset U
  actions_nonempty : ∀ i, (actions i).Nonempty
  p : S → U → S → ℝ
  p_nonneg : ∀ i a j, a ∈ actions i → 0 ≤ p i a j
  p_sum : ∀ i a, a ∈ actions i → ∑ j, p i a j = 1
  F : S → U → S → Measure ℝ
  F_prob : ∀ i a j, a ∈ actions i → IsProbabilityMeasure (F i a j)
  F_nonneg : ∀ i a j, a ∈ actions i → F i a j (Set.Iio 0) = 0
  r : S → U → ℝ
  s : S → U → ℝ

end KallenbergLP.SemiMarkov
