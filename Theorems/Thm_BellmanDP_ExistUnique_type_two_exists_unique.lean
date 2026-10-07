import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes

open Filter Topology

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 4, Theorem 2, p. 121. If
`f(p) = Sup_q [g(p, q) + h(p, q) f(T(p, q))]` is an equation of Type Two, there is a unique
solution on `D` which is bounded in any finite part of `D`; it is the limit of the successive
approximations (4.3) from `f₀(p) = Sup_q g(p, q)`; and it is continuous on every bounded portion
of `D` when `g`, `h`, `T` are continuous in `p` on bounded portions of `D` uniformly in `q`. -/
theorem type_two_exists_unique {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N))
    (hType : TypeTwo D g h T) :
    ∃ f : EuclideanSpace ℝ (Fin N) → ℝ,
      (BoundedOnBoundedParts D f ∧ ∀ p ∈ D, SolvesAt g h T f p) ∧
      (∀ F : EuclideanSpace ℝ (Fin N) → ℝ, BoundedOnBoundedParts D F →
        (∀ p ∈ D, SolvesAt g h T F p) → ∀ p ∈ D, F p = f p) ∧
      (∀ p ∈ D, Tendsto (fun n => succApprox g h T (supG g) n p) atTop (𝓝 (f p))) ∧
      (UnifContInP D g → UnifContInP D h → UnifContInP D T →
        ∀ c : ℝ, ContinuousOn f (D ∩ Metric.closedBall 0 c)) := by sorry

end BellmanDP.ExistUnique

