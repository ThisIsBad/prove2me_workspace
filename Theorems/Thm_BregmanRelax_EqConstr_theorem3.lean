import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_EqConstr_Program

namespace BregmanRelax.EqConstr

/-- Theorem 3 (Bregman 1967, pp. 209–210). Standing hypotheses of §2: `f` strictly convex and
continuously differentiable over the convex set `S ⊆ E^p` (gradient map `g`), continuous over `S̄`;
all rows `a i` of `A` nonzero; the feasible set `R = {Ax = b} ∩ S̄` nonempty; `D` of (1.4) satisfies
conditions I–VI (with the D-projection map `P` onto the hyperplanes `A_i`) and condition (2).
If `P` maps interior points of `S` to interior points of `S`, then for every relaxation control
`i` and every relaxation sequence `x` started at `x 0 ∈ Z ∩ int S` that converges to a point
`x* ∈ R`, the point `x*` minimizes `f` over `R`. -/
theorem theorem3 {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hS : Convex ℝ S) (hfc : StrictConvexOn ℝ S f)
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x) (hgc : ContinuousOn g S)
    (hfcl : ContinuousOn f (closure S))
    (ha : ∀ i, a i ≠ 0)
    (hRne : (feasibleEq a b S).Nonempty)
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    (hV : BregmanRelax.Cyclic.CondV S (bregmanD f g) (feasibleEq a b S ∩ S))
    (h2 : Cond2 S (bregmanD f g))
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S)
    (i : ℕ → Fin m) (x : ℕ → EuclideanSpace ℝ (Fin p)) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x)
    (hx0 : x 0 ∈ Zset S g a ∩ interior S)
    (x' : EuclideanSpace ℝ (Fin p)) (hlim : Filter.Tendsto x Filter.atTop (nhds x'))
    (hx'R : x' ∈ feasibleEq a b S) :
    ∀ y ∈ feasibleEq a b S, f x' ≤ f y := by sorry

end BregmanRelax.EqConstr

