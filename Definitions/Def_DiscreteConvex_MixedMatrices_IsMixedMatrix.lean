import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.353-354, Eq. (12.7), axioms (M-Q), (M-T): the
definition of a mixed matrix, in `DiscreteConvex.MixedMatrices`.
-/

namespace DiscreteConvex.MixedMatrices

/-- `A = Q + T` (Eq. (12.7)) is a **mixed matrix** with respect to `(K, F)` (`K` a subfield of
`F`, realized as `Algebra K F`): `Q` is a matrix over `K` (axiom (M-Q)) embedded into `F` via the
structure map, `T` is a matrix over `F` (axiom (M-T)), and the family of `T`'s nonzero entries is
algebraically independent over `K`. The "usually assume `Tᵢⱼ ≠ 0 ⟹ Qᵢⱼ = 0`" normalization the
book adds immediately after Eq. (12.7) (for uniqueness of the decomposition `Q + T`) is not part
of this predicate: it is a convention for representing a given mixed matrix, not a hypothesis any
of this chapter's theorems (12.6-12.9) need. -/
def IsMixedMatrix {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F] [Algebra K F]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) : Prop :=
  (∀ i j, A i j = algebraMap K F (Q i j) + T i j) ∧
  AlgebraicIndependent K (fun e : {p : R × C // T p.1 p.2 ≠ 0} => T e.1.1 e.1.2)

end DiscreteConvex.MixedMatrices
