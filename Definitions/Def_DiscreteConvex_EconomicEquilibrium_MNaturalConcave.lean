import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_UDom

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.330, Eq. (11.17), axiom (−M♮-EXC[Z]): the direct
definition of an M♮-concave function (licensed by Theorem 6.2, as the book itself recalls at the
start of section 11.3), in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

open DiscreteConvex.MConvexFunctions

/-- `U : Zᴷ → R ∪ {−∞}` with `dom U ≠ ∅` is **M♮-concave** if it satisfies the exchange axiom
**(−M♮-EXC[Z])** (Eq. (11.17)): for `x, y ∈ dom U` and `i ∈ supp⁺(x-y)`,
`U(x) + U(y) ≤ max(U(x - χ_i) + U(y + χ_i), max_{j ∈ supp⁻(x-y)}[U(x - χ_i + χ_j) + U(y + χ_i -
χ_j)])`, where a maximum over an empty set is `−∞` (matching the book's stated convention, and
realized here by `Finset.sup`'s default value `⊥` on `WithBot ℝ`). -/
def MNaturalConcave {K : Type*} [Fintype K] [DecidableEq K] (U : (K → ℤ) → WithBot ℝ) : Prop :=
  (UDom U).Nonempty ∧
  ∀ x ∈ UDom U, ∀ y ∈ UDom U, ∀ i ∈ SuppPos x y,
    U x + U y ≤ max (U (fun w => x w - CharVec i w) + U (fun w => y w + CharVec i w))
      ((SuppNeg x y).sup (fun j =>
        U (fun w => x w - CharVec i w + CharVec j w) +
          U (fun w => y w + CharVec i w - CharVec j w)))

end DiscreteConvex.EconomicEquilibrium
