import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

namespace Disjunctive.Dominants

/-- Corollary 13.8 (Balas §13.2, p. 221): every inequality `πx≥β` defining a facet of `P⁺` has at
most `dim(P)+1` nonzero coefficients. -/
theorem facet_support_bound {n : ℕ} (P : Set (Fin n → ℝ)) (pi : Fin n → ℝ) (beta : ℝ)
    (hfacet : IsFacet (Dominant P) ({x ∈ Dominant P | dotProduct pi x = beta})) :
    ((Finset.univ.filter (fun j => pi j ≠ 0)).card : ℤ) ≤ PolyDim P + 1 := by sorry

end Disjunctive.Dominants

