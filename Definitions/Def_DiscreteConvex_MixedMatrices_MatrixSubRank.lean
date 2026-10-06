import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.357 (the submatrix notation `A[I,J]` and its
rank, used throughout section 12.3), in `DiscreteConvex.MixedMatrices`.
-/

namespace DiscreteConvex.MixedMatrices

/-- The rank of the submatrix `M[I,J]` of `M : Matrix R C 𝔽` with row indices in `I ⊆ R` and
column indices in `J ⊆ C`. -/
noncomputable def MatrixSubRank {R C 𝔽 : Type*} [Fintype R] [Fintype C] [Field 𝔽]
    (M : Matrix R C 𝔽) (I : Finset R) (J : Finset C) : ℕ :=
  (M.submatrix ((↑) : I → R) ((↑) : J → C)).rank

end DiscreteConvex.MixedMatrices
