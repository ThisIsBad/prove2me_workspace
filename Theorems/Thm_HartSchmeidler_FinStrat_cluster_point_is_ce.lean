import Definitions.Def_HartSchmeidler_FinStrat_Game

namespace HartSchmeidler.FinStrat

open MeasureTheory

/-- Proof of Theorem 2(ii), p. 23: an anchored f-set equilibrium family passes
condition (3) to any cluster point against continuous real test functions. -/
theorem cluster_point_is_ce {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]
    (h : ι → (∀ i, S i) → ℝ) (hh : ∀ i, Continuous (h i))
    (anchor : ∀ i, S i)
    (F : (∀ i, Finset (S i)) → Finset (∀ i, S i))
    (w : (∀ i, Finset (S i)) → (∀ i, S i) → ℝ)
    (hFw : ∀ T, IsAnchoredFSet anchor T → IsFSetCE h T (F T) (w T))
    (p : Measure (∀ i, S i)) (hp : IsProbabilityMeasure p)
    (hcluster : ∀ (f : C(∀ i, S i, ℝ)) (ε : ℝ), 0 < ε →
      ∀ T₀, IsAnchoredFSet anchor T₀ →
        ∃ T, IsAnchoredFSet anchor T ∧ FSetLE T₀ T ∧
          |∫ s, f s ∂p - ∑ s ∈ F T, w T s * f s| < ε) :
    IsCorrelatedEq h p := by sorry

end HartSchmeidler.FinStrat

