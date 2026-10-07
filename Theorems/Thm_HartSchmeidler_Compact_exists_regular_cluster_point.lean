import Mathlib

namespace HartSchmeidler.Compact

open MeasureTheory

/-- Proof of Theorem 3, p. 24 (Banach–Alaoglu step): on a compact Hausdorff space with its Borel
σ-algebra, every net of probability measures indexed by a nonempty directed set has a cluster
point, for the topology induced by the continuous functions, that is a regular probability
measure. -/
theorem exists_regular_cluster_point {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {D : Type*} [Preorder D] [IsDirected D (· ≤ ·)] [Nonempty D]
    (q : D → Measure X) (hq : ∀ d, IsProbabilityMeasure (q d)) :
    ∃ p : Measure X, IsProbabilityMeasure p ∧ p.Regular ∧
      ∀ (fs : Finset C(X, ℝ)) (ε : ℝ), 0 < ε → ∀ d₀ : D, ∃ d : D, d₀ ≤ d ∧
        ∀ f ∈ fs, |∫ x, f x ∂p - ∫ x, f x ∂(q d)| < ε := by sorry

end HartSchmeidler.Compact

