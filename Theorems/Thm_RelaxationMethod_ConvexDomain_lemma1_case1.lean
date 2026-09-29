import Mathlib
import Definitions.Def_RelaxationMethod_Shared_FejerMonotone
open Filter Topology

namespace RelaxationMethod.ConvexDomain

/-- Lemma 1, Case 1, p. 397: a sequence that is Fejér-monotone with respect to a set `A` of
dimension `n` (its affine span is the whole space `E_n`) converges to a point. Stated for an
arbitrary set `A`; the paper states it for the polytope (1.4) and applies it in §10 to a closed
bounded convex set. -/
theorem lemma1_case1 {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hspan : affineSpan ℝ A = ⊤) (q : ℕ → EuclideanSpace ℝ (Fin n))
    (hq : RelaxationMethod.Shared.IsFejerMonotone A q) :
    ∃ l : EuclideanSpace ℝ (Fin n), Tendsto q atTop (𝓝 l) := by sorry

end RelaxationMethod.ConvexDomain

