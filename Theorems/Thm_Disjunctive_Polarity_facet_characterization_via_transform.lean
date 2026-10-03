import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_Transform

namespace Disjunctive.Polarity

/-- Proposition 2.11 ([14], Balas §2.3, p. 32): if `Proj_x(Q)` is full-dimensional, `vx ≤ v0`
defines a facet of `Proj_x(Q)` if and only if `(v,v0)` is an extreme ray of `Proj_{(v,v0)}(W̃)`,
where `W̃` is the projection cone of the transformed system `Q̃` obtained from `Q` by replacing
`B` with the identity. The transformation is cited from [14] and not spelled out on the page, so
`W̃` is carried by the properties the page states for it: a pointed convex cone whose *extreme
rays* give the representation `Proj_x(Q̃) = {x : vx ≤ v0 for all (v,w,v0) ∈ extr W̃}`, with
`Proj_x(Q̃) = Proj_x(Q)`. Quantifying instead over an arbitrary set satisfying a representation
by all of `Proj_{(v,v0)}(W̃)` makes the statement false: a finite generating set of valid
inequalities represents `Proj_x(Q)` and has no extreme rays at all. -/
theorem facet_characterization_via_transform {m p q w : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (Wt : Set ((Fin q → ℝ) × (Fin w → ℝ) × ℝ))
    (hFullDim : PolyDim (ProjOntoX (Poly2 A B b)) = (q : ℤ))
    (hWt_convex : Convex ℝ Wt)
    (hWt_cone : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ Wt, t • z ∈ Wt)
    (hWt_pointed : ∀ z ∈ Wt, -z ∈ Wt → z = 0)
    (hRepr : ProjOntoX (Poly2 A B b) =
      {x | ∀ v ww v0, IsExtremeRay Wt (v, ww, v0) → dotProduct v x ≤ v0})
    (v : Fin q → ℝ) (v0 : ℝ) :
    IsFacet (ProjOntoX (Poly2 A B b))
        (ProjOntoX (Poly2 A B b) ∩ {x | dotProduct v x = v0}) ↔
      IsExtremeRay (ProjVW Wt) (v, v0) := by sorry

end Disjunctive.Polarity

