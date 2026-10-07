import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes

open Filter Topology

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 3, Theorem 1, pp. 119–120. For an equation
`f(p) = Sup_q [g(p, q) + h(p, q) f(T(p, q))]` (`p ≠ θ`), `f(θ) = 0`, of Type One:
1. there is exactly one solution on `D` that is continuous at `p = θ` (within `D`) and equal to
   zero there;
2. it is the limit of the successive approximations (3) started from `f₀(p) = Sup_q g(p, q)`;
3. any `f₀` continuous at `θ`, zero there, and bounded on `{p ∈ D : ‖p‖ ≤ c₁}` for every `c₁`
   also yields a sequence (3b) converging to it;
4. if `g`, `h`, `T` are continuous in `p` on bounded portions of `D`, uniformly for all `q ∈ S`,
   the solution is continuous on every bounded portion of `D`. -/
theorem type_one_exists_unique {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N)) (a : ℝ)
    (hType : TypeOne D g h T a) :
    ∃ f : EuclideanSpace ℝ (Fin N) → ℝ,
      (ContinuousWithinAt f D 0 ∧ f 0 = 0 ∧ ∀ p ∈ D, p ≠ 0 → SolvesAt g h T f p) ∧
      (∀ F : EuclideanSpace ℝ (Fin N) → ℝ, ContinuousWithinAt F D 0 → F 0 = 0 →
        (∀ p ∈ D, p ≠ 0 → SolvesAt g h T F p) → ∀ p ∈ D, F p = f p) ∧
      (∀ p ∈ D, Tendsto (fun n => succApprox g h T (supG g) n p) atTop (𝓝 (f p))) ∧
      (∀ f₀ : EuclideanSpace ℝ (Fin N) → ℝ, ContinuousWithinAt f₀ D 0 → f₀ 0 = 0 →
        BoundedOnBoundedParts D f₀ →
        ∀ p ∈ D, Tendsto (fun n => succApprox g h T f₀ n p) atTop (𝓝 (f p))) ∧
      (UnifContInP D g → UnifContInP D h → UnifContInP D T →
        ∀ c : ℝ, ContinuousOn f (D ∩ Metric.closedBall 0 c)) := by sorry

end BellmanDP.ExistUnique

