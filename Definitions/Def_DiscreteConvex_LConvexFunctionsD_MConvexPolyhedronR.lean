import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsPolyhedronW

namespace DiscreteConvex.LConvexFunctionsD

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class `M⁰[R]` of **real** M-convex polyhedra: a polyhedron satisfying the real exchange
axiom (B-EXC[R]). `MConvexPolyhedron` is the convex hull of an integer M-convex set, i.e. the
*integral* class `M⁰[Z|R]`. Theorem 7.45 (c) concludes in the real class: the subdifferential of
`g(p) = (1/2) max(p₁ - p₂, 0)` at `0` is the segment from `(0,0)` to `(1/2,-1/2)`, which is the
convex hull of no integer set. -/
def MConvexPolyhedronR (P : Set (V → ℝ)) : Prop :=
  IsPolyhedronW P ∧
    ∀ x ∈ P, ∀ y ∈ P, ∀ i : V, 0 < x i - y i →
      ∃ j : V, x j - y j < 0 ∧ ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
        (fun v => x v - α * ((if v = i then (1 : ℝ) else 0) - (if v = j then 1 else 0))) ∈ P ∧
        (fun v => y v + α * ((if v = i then (1 : ℝ) else 0) - (if v = j then 1 else 0))) ∈ P

end DiscreteConvex.LConvexFunctionsD
