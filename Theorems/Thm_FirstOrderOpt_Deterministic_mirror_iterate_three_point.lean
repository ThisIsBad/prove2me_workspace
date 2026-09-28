import Mathlib

namespace FirstOrderOpt.Deterministic

/-- Lemma 3.4 (three-point inequality for the mirror-descent update). Given `xt` and a
subgradient functional `gt` of `f` at `xt`, `xt1` minimizes `u ↦ γt·gt(u) + V(xt,u)` over `X`
(the update (3.2.5)); then for every `x ∈ X`, `γt·gt(xt1-x) + V(xt,xt1) ≤ V(xt,x) - V(xt1,x)`. As
in Lemma 3.1, the book quantifies over `y ∈ X` but uses `x` in the body; read as a single free
variable. `V` is pinned down to a genuine Bregman divergence (nonnegative, satisfying the
three-point/cosine identity (3.2.6) via its gradient-in-second-argument `dV`), since the
book's proof of this lemma needs both facts and neither holds for an arbitrary `V : E → E → ℝ`. -/
theorem mirror_iterate_three_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (V : E → E → ℝ) (dV : E → E → E →L[ℝ] ℝ) (xt xt1 : E) (gt : E →L[ℝ] ℝ) (γt : ℝ)
    (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (hVnonneg : ∀ x ∈ X, ∀ z ∈ X, 0 ≤ V x z)
    (hVthreepoint : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, V x z = V x y + (dV x y) (z - y) + V y z)
    (hmin : ∀ x ∈ X, γt * gt xt1 + V xt xt1 ≤ γt * gt x + V xt x) :
    ∀ x ∈ X, γt * gt (xt1 - x) + V xt xt1 ≤ V xt x - V xt1 x := by sorry

end FirstOrderOpt.Deterministic
