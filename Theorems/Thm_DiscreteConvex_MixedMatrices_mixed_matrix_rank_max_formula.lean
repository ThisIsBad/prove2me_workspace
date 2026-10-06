import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank


namespace DiscreteConvex.MixedMatrices

/-- Theorem 12.7 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.357), Eq. (12.9). For a mixed
matrix `A = Q + T`, `rank A = max{rank Q[I,J] + rank T[R\I,C\J] | I ⊆ R, J ⊆ C}`. -/
theorem mixed_matrix_rank_max_formula {R C K F : Type*} [Fintype R] [Fintype C] [Field K]
    [Field F] [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T) :
    A.rank = (Finset.univ : Finset (Finset R)).sup (fun I =>
      (Finset.univ : Finset (Finset C)).sup (fun J =>
        MatrixSubRank Q I J + MatrixSubRank T Iᶜ Jᶜ)) := by sorry

end DiscreteConvex.MixedMatrices

