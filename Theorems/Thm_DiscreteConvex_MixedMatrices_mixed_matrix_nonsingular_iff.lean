import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_IsNonsingularSub


namespace DiscreteConvex.MixedMatrices

/-- Proposition 12.6 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.357). A square mixed
matrix `A = Q + T` is nonsingular if and only if there exist `I ⊆ R` and `J ⊆ C` such that both
`Q[I,J]` and `T[R\I,C\J]` are nonsingular. -/
theorem mixed_matrix_nonsingular_iff {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T)
    (hsq : Fintype.card R = Fintype.card C) :
    IsNonsingularSub A (Finset.univ : Finset R) (Finset.univ : Finset C) ↔
      ∃ I : Finset R, ∃ J : Finset C, IsNonsingularSub Q I J ∧ IsNonsingularSub T Iᶜ Jᶜ := by sorry

end DiscreteConvex.MixedMatrices

