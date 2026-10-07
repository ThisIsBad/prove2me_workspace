import Definitions.Def_HartSchmeidler_FinStrat_Game

namespace HartSchmeidler.FinStrat

open MeasureTheory

/-- Proof of Theorem 2(ii), p. 23: a directed family of probability measures on
the compact product has a cluster point for the weak topology induced by C(S).
Finite collections of tests describe a genuine weak neighborhood. -/
theorem exists_cluster_point {ι : Type*} [Nonempty ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]
    {D : Type*} [Preorder D] [IsDirected D (· ≤ ·)] [Nonempty D]
    (q : D → Measure (∀ i, S i)) (hq : ∀ d, IsProbabilityMeasure (q d)) :
    ∃ p : Measure (∀ i, S i), IsProbabilityMeasure p ∧
      ∀ (fs : Finset C(∀ i, S i, ℝ)) (ε : ℝ), 0 < ε → ∀ d₀ : D,
        ∃ d : D, d₀ ≤ d ∧
          ∀ f ∈ fs, |∫ s, f s ∂p - ∫ s, f s ∂(q d)| < ε := by sorry

end HartSchmeidler.FinStrat

