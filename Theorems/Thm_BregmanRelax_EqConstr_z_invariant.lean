import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_EqConstr_Program

namespace BregmanRelax.EqConstr

/-- Proof of Theorem 3 (Bregman 1967, p. 210), the sentence after (2.8): under the hypotheses of
(2.7)–(2.8), the D-projection onto any `A_i` maps `Z ∩ int S` into `Z ∩ int S`. -/
theorem z_invariant {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x)
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S) :
    ∀ i, ∀ x ∈ Zset S g a ∩ interior S, P i x ∈ Zset S g a ∩ interior S := by sorry

end BregmanRelax.EqConstr

