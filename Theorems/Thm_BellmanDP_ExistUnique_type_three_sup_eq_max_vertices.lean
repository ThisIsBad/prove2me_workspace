import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_TypeThree

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 8, Lemma 2, p. 127. Under the hypotheses of
Theorem 5, for any two bounded solutions `f`, `g` of (8.1),
`Sup_p |f(p) − g(p)| = Max_k |f(x_k) − g(x_k)|`, the supremum over the simplex. -/
theorem type_three_sup_eq_max_vertices (n M : ℕ)
    (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (c₁ : ℝ)
    (hT : TypeThreeHyp n M Tr c₁) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hf_bdd : BoundedOnSimplex n f) (hf : SolvesTypeThree n M Tr f)
    (hg_bdd : BoundedOnSimplex n g) (hg : SolvesTypeThree n M Tr g) :
    IsLUB ((fun p => |f p - g p|) '' simplex n)
      (⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)|) := by sorry

end BellmanDP.ExistUnique

