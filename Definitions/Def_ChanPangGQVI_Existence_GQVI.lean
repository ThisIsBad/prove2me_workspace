import Mathlib

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence

/-- Chan and Pang, *The generalized quasi-variational inequality problem*, Math. Oper. Res. 7
(1982), p. 212, §2. Given point-to-set mappings `K` and `f` of `ℝⁿ` into itself, a solution of
the generalized quasi-variational inequality problem `GQVI(K, f)` is a pair `(x, y)` with
`x ∈ K(x)`, `y ∈ f(x)` and `(x' - x)ᵀ y ≥ 0` for all `x' ∈ K(x)`. -/
def IsGQVISolution {n : ℕ}
    (K f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ K x ∧ y ∈ f x ∧ ∀ x' ∈ K x, 0 ≤ ⟪x' - x, y⟫

/-- The point-to-set mapping `μ + q : x ↦ {y + q : y ∈ μ(x)}` (Chan and Pang 1982, §4, p. 217,
Theorem 4.1: "the GQVI(K, μ + q)"). -/
def shiftMap {n : ℕ}
    (μ : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (q : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)) :=
  fun x => (fun y => y + q) '' μ x

end ChanPangGQVI.Existence
