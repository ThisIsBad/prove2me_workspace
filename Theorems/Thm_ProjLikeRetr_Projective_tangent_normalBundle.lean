import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

namespace ProjLikeRetr.Projective

/-- (3.3), proof of Lemma 3.1, p. 7: the tangent space at `(x̄, 0)` of the normal bundle `NM`
(a `C^{k-1}` submanifold of `E × E`) is `T_M(x̄) × N_M(x̄)`. -/
theorem tangent_normalBundle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (hk : 2 ≤ k) (M : Set E) (xbar : E)
    (hM : ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) :
    Submodule.span ℝ (tangentConeAt ℝ (ProjLikeRetr.Retractor.normalBundle M) (xbar, 0)) =
      (ProjLikeRetr.Retractor.tangentSpace M xbar).prod (ProjLikeRetr.Retractor.normalSpace M xbar) := by sorry

end ProjLikeRetr.Projective

