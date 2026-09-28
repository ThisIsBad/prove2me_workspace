import Mathlib

namespace FirstOrderOpt.Stochastic

/-- Lemma 3.4 (three-point inequality), restated for the stochastic mirror-descent update as
invoked at p. 115: "It can be easily seen that the result in Lemma 3.4 holds with `gt` replaced
by `Gt`." `xt1` minimizes `u ↦ γt·Gt(u) + V(xt,u)` over `X` (the stochastic update (4.1.6), the
same three-point-defining minimality as (3.2.5) with the stochastic gradient functional `Gt` in
place of the deterministic subgradient `gt`); then for every `x ∈ X`,
`γt·Gt(xt1-x) + V(xt,xt1) ≤ V(xt,x) - V(xt1,x)`. As in Lemma 3.4 itself, the book quantifies over
`y ∈ X` but uses `x` in the body; read as a single free variable. Restated locally in this
sub-namespace (rather than imported from `FirstOrderOpt.Deterministic`) because chunk
`03-deterministic`'s `mirror_iterate_three_point` is itself an unpublished draft; see
`MODERATION_NOTES.md`. -/
theorem stochastic_mirror_iterate_three_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (V : E → E → ℝ) (xt xt1 : E) (Gt : E →L[ℝ] ℝ) (γt : ℝ)
    (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * Gt xt1 + V xt xt1 ≤ γt * Gt x + V xt x) :
    ∀ x ∈ X, γt * Gt (xt1 - x) + V xt xt1 ≤ V xt x - V xt1 x := by sorry

end FirstOrderOpt.Stochastic
