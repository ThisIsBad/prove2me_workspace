import Mathlib

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour p. 516: a branch-decomposition `(T, L)` of a set function on the finite ground set
`V`. `T` is a subcubic tree — a tree with at least two vertices, every vertex incident with at most
three edges — here on the vertex set `Fin n`; `L` is a bijection from `V` onto the set of leaves
(vertices incident with exactly one edge) of `T`. -/
structure BranchDecomp (V : Type*) where
  /-- number of vertices of the tree `T` -/
  n : ℕ
  /-- the tree -/
  T : SimpleGraph (Fin n)
  isTree : T.IsTree
  two_le : 2 ≤ n
  subcubic : ∀ t : Fin n, (T.neighborSet t).ncard ≤ 3
  /-- the labelling of the leaves by elements of `V` -/
  L : V → Fin n
  L_leaf : ∀ v : V, (T.neighborSet (L v)).ncard = 1
  L_injective : Function.Injective L
  L_surjective : ∀ t : Fin n, (T.neighborSet t).ncard = 1 → ∃ v : V, L v = t

namespace BranchDecomp

variable {V : Type*} [Fintype V]

/-- For an edge `uw` of `T`, the set `L⁻¹(X)` of elements of `V` whose leaf lies in the component
of `T \ uw` containing `u`. -/
noncomputable def side (D : BranchDecomp V) (u w : Fin D.n) : Finset V := by
  classical
  exact Finset.univ.filter (fun x : V => (D.T.deleteEdges {s(u, w)}).Reachable u (D.L x))

/-- Oum–Seymour p. 516: `(T, L)` has width at most `k` with respect to `f`: for every edge `uw`
of `T`, the width `f(L⁻¹(X))` of the edge is at most `k`, where `X` is the set of leaves on
either side of the edge (both sides are constrained, so no side is privileged). -/
def WidthLE (D : BranchDecomp V) (f : Finset V → ℤ) (k : ℤ) : Prop :=
  ∀ u w : Fin D.n, D.T.Adj u w → f (D.side u w) ≤ k

end BranchDecomp

/-- `bw(f) ≤ k`, Oum–Seymour p. 516: either `|V| ≤ 1`, where the paper sets `bw(f) = f(∅)`, and
`f(∅) ≤ k`; or `f` has a branch-decomposition of width at most `k`. Stated as a predicate so that
no minimum over a possibly empty family is ever taken. -/
def BwLE {V : Type*} [Fintype V] (f : Finset V → ℤ) (k : ℤ) : Prop :=
  (Fintype.card V ≤ 1 ∧ f ∅ ≤ k) ∨ ∃ D : BranchDecomp V, D.WidthLE f k

end ApproxCliqueWidth.Certificate
