import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

open RandomGradFree.Nonsmooth

namespace ProjLikeRetr.Projective

/-- Lemma 3.1, p. 7 (Projection onto a manifold): if `M` is a `C^k` submanifold (`k ≥ 2`)
around `x̄ ∈ M`, then on some ball `B(x̄, δ)` the projection `P_M(x)` (the set of nearest points
of `M` to `x`) is a single point `P x`, the map `P` is `C^{k-1}` on that ball, and
`DP(x̄) = P_{T_M(x̄)}`, the orthogonal projector onto the tangent space. -/
theorem lemma_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    ∃ δ > 0, ∃ P : E → E,
      (∀ x ∈ Metric.ball xbar δ, {z | IsMetricProjection M x z} = {P x}) ∧
      ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) P (Metric.ball xbar δ) ∧
      HasFDerivAt P (ProjLikeRetr.Retractor.tangentSpace M xbar).starProjection xbar := by sorry

end ProjLikeRetr.Projective

