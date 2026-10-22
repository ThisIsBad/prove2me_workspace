import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedron

namespace DiscreteConvex.NetworkFlowsB

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class `L⁰[R]` of **real** L-convex polyhedra: a nonempty polyhedron closed under `⊔`, `⊓`
and translation by any multiple of the all-ones vector — the indicator form of (SBF[R]) and
(TRF[R]). `LConvexPolyhedron` is the convex hull of an integer L-convex set, i.e. the *integral*
class `L⁰[Z|R]`. Theorem 9.6 (2) and Theorem 9.15 (1) hold in the real class: one arc of cost
`1/2` gives optimal potentials `{p : p(v) - p(u) ≤ 1/2}`, the convex hull of no integer set. -/
def LConvexPolyhedronR (P : Set (V → ℝ)) : Prop :=
  IsPolyhedron P ∧ P.Nonempty ∧
    (∀ p ∈ P, ∀ q ∈ P, p ⊔ q ∈ P ∧ p ⊓ q ∈ P) ∧
    (∀ p ∈ P, ∀ α : ℝ, (fun v => p v + α) ∈ P)

end DiscreteConvex.NetworkFlowsB
