import Definitions.Def_TopkisRation_Myopic_MultiPeriod

namespace TopkisRation.Myopic

variable {n : ℕ}

/-- The General Case, pp. 174–175: the continuation and ordering cost functions are convex and continuous. -/
theorem C_convex_continuous (Q : MultiModel n) (hQ : Q.Standing) :
    (∀ m ∈ Finset.Icc 1 (Q.N + 1),
      ConvexOn ℝ Set.univ (Q.C m) ∧ Continuous (Q.C m)) ∧
    (∀ m ∈ Finset.Icc 1 Q.N,
      ConvexOn ℝ (Set.Ici 0) (Q.gtilde m) ∧ ContinuousOn (Q.gtilde m) (Set.Ici 0)) := by sorry

end TopkisRation.Myopic

