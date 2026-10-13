import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_QuadraticFormRestricted
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_QuadraticFormTotal


/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.139, Proposition 6.8, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Proposition 6.8 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.139). See the item's
`natural_language_statement` for the full statement. -/
theorem quadratic_form_mconvex_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (r : ℤ) :
    (MExchangeAxiom (QuadraticFormRestricted n A r) ↔
      ∀ i j k l : Fin n, Disjoint ({i, j} : Finset (Fin n)) ({k, l} : Finset (Fin n)) →
        A i j + A k l ≥ min (A i k + A j l) (A i l + A j k)) ∧
    (MNaturalConvex (QuadraticFormTotal n A) ↔
      (∀ i j k l : Fin n, Disjoint ({i, j} : Finset (Fin n)) ({k, l} : Finset (Fin n)) →
        A i j + A k l ≥ min (A i k + A j l) (A i l + A j k)) ∧
      (∀ i j k : Fin n, Disjoint ({i, j} : Finset (Fin n)) ({k} : Finset (Fin n)) →
        A i j ≥ min (A i k) (A j k)) ∧
      (∀ i j : Fin n, A i j ≥ 0)) := by sorry

end DiscreteConvex.MConvexFunctionsB

