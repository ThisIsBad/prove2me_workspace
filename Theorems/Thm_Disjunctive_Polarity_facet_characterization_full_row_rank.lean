import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection

namespace Disjunctive.Polarity

/-- Corollary 2.12 ([14], Balas §2.3, p. 32): when `B` has full row rank, the auxiliary
`w`-coordinate of Proposition 2.11's transformed cone is unnecessary, and `vx ≤ v0` defines a
facet of `Proj_x(Q)` if and only if `(v,v0)` is directly an extreme ray of `W̃` (here `Wt`, taken
via its defining relation `hRepr`, as in Proposition 2.11). -/
theorem facet_characterization_full_row_rank {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (Wt : Set ((Fin q → ℝ) × ℝ))
    (hFullDim : PolyDim (ProjOntoX (Poly2 A B b)) = (q : ℤ)) (hFullRowRank : B.rank = m)
    (hRepr : ProjOntoX (Poly2 A B b) = {x | ∀ v v0, (v, v0) ∈ Wt → dotProduct v x ≤ v0})
    (v : Fin q → ℝ) (v0 : ℝ) :
    IsFacet (ProjOntoX (Poly2 A B b))
        (ProjOntoX (Poly2 A B b) ∩ {x | dotProduct v x = v0}) ↔
      IsExtremeRay Wt (v, v0) := by sorry

end Disjunctive.Polarity

