import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedPolyMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_SubDegDet


namespace DiscreteConvex.MixedMatrices

/-- Theorem 12.13 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.360), Eq. (12.14). For a
square mixed polynomial matrix `A(s) = Q(s) + T(s)`,
`deg det A = max{deg det Q[I,J] + deg det T[R\I,C\J] | |I| = |J|, I ⊆ R, J ⊆ C}`, where both sides
are `−∞` if `A` is singular (i.e. `det A(s)` is the zero polynomial; `Polynomial.degree`'s `⊥`
realizes `−∞` throughout). -/
theorem mixed_poly_matrix_deg_det_max_formula {R K F : Type*} [Fintype R] [Field K] [Field F]
    [Algebra K F] [DecidableEq R]
    (A : Matrix R R (Polynomial F)) (Q : Matrix R R (Polynomial K)) (T : Matrix R R (Polynomial F))
    (hA : IsMixedPolyMatrix A Q T) :
    (Matrix.det A).degree =
      ((Finset.univ : Finset (Finset R × Finset R)).filter
          (fun p => p.1.card = p.2.card)).sup
        (fun p => SubDegDet Q p.1 p.2 + SubDegDet T p.1ᶜ p.2ᶜ) := by sorry

end DiscreteConvex.MixedMatrices

