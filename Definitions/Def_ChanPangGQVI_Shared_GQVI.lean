import Mathlib

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Shared

/-- Chan and Pang, *The generalized quasi-variational inequality problem*, Math. Oper. Res. 7
(1982), p. 212, §2. Given point-to-set mappings `K` and `f` of `ℝⁿ` into itself, a solution of
the generalized quasi-variational inequality problem `GQVI(K, f)` is a pair `(x, y)` with
`x ∈ K(x)`, `y ∈ f(x)` and `(x' - x)ᵀ y ≥ 0` for all `x' ∈ K(x)`. A point-to-point `f` enters
as the singleton-valued mapping `fun z => {f z}`. -/
def IsGQVISolution {n : ℕ}
    (K f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ K x ∧ y ∈ f x ∧ ∀ x' ∈ K x, 0 ≤ ⟪x' - x, y⟫

end ChanPangGQVI.Shared
