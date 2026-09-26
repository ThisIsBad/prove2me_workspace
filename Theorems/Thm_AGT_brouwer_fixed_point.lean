import Mathlib

namespace AGT

/-- **Brouwer fixed-point theorem** (supporting result for Theorem 1.8 of
*Algorithmic Game Theory*; the book invokes it without proof for Nash's
theorem).  Every continuous self-map of a nonempty compact convex subset of a
finite-dimensional real normed space has a fixed point.

The nonemptiness hypothesis is essential: the empty set is compact and
convex, and the (empty) self-map of it has no fixed point.  Mathlib currently
has no form of this theorem, which is precisely why it is worth having as a
milestone. -/
theorem brouwer_fixed_point {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E}
    (hKconv : Convex ℝ K) (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  sorry

end AGT