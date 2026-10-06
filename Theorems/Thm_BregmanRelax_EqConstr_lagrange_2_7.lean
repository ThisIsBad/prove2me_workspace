import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_EqConstr_Program

namespace BregmanRelax.EqConstr

/-- (2.7)–(2.8), proof of Theorem 3 (Bregman 1967, p. 210): if `P` is the D-projection map of
condition II for the hyperplanes `A_i` and `D` of (1.4), and `P` maps interior points of `S` to
interior points of `S`, then for every interior point `x` of `S` the D-projection `P i x` onto `A_i`
satisfies `g(P i x) = g(x) + λ A_i` for some real `λ` (named `lam`) and `(A_i, P i x) = b_i`. -/
theorem lagrange_2_7 {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x)
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S) :
    ∀ i, ∀ x ∈ interior S, ∃ lam : ℝ,
      g (P i x) = g x + lam • a i ∧ inner ℝ (a i) (P i x) = b i := by sorry

end BregmanRelax.EqConstr

