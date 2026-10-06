import Mathlib
import Definitions.Def_BregmanRelax_EqConstr_Program

namespace BregmanRelax.EqConstr

/-- Lemma 3 (Bregman 1967, p. 209): a feasible point `y*` of problem (2.1)–(2.3) that lies in the
closure of `Z` minimizes `f` over the feasible set `R = {x | Ax = b} ∩ S̄`. -/
theorem lemma3 {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    (hS : Convex ℝ S) (hfc : StrictConvexOn ℝ S f)
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x) (hgc : ContinuousOn g S)
    (hfcl : ContinuousOn f (closure S))
    (h2 : Cond2 S (bregmanD f g))
    (y' : EuclideanSpace ℝ (Fin p)) (hyR : y' ∈ feasibleEq a b S)
    (hyZ : y' ∈ closure (Zset S g a)) :
    ∀ x ∈ feasibleEq a b S, f y' ≤ f x := by sorry

end BregmanRelax.EqConstr

