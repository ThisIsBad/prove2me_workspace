import Mathlib

open Filter Topology

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §2, pp. 74–75: the standing class of the theorem. `G ⊆ ℝⁿ` is a nonempty
convex set, `f` (only its values on `G` matter) is convex on `G` and semi-continuous from below
on `G`, and `G` is closed relative to `f`: at every boundary point of `G` not belonging to `G`
(i.e. every point of `closure G \ G`), `f(x) → ∞` as `x → x*` inside `G`. -/
def IsClosedConvexPair {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  G.Nonempty ∧ ConvexOn ℝ G f ∧ LowerSemicontinuousOn f G ∧
    ∀ x ∈ closure G \ G, Tendsto f (𝓝[G] x) atTop

end ConjugateConvex.Involution
