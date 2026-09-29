import Mathlib

namespace ApproxCliqueWidth.Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Oum–Seymour Definition 6.1 (p. 522): `cutrk*_G(X, Y) = rk(A(G)[X, Y])`, the rank over
`GF(2)` of the submatrix of the adjacency matrix of `G` with rows `X` and columns `Y`.
The paper defines it for disjoint `X, Y`; the formula makes sense for all pairs. -/
noncomputable def cutrkStar (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : ℤ :=
  (((G.adjMatrix (ZMod 2)).submatrix (fun x : X => (x : V)) (fun y : Y => (y : V))).rank : ℤ)

/-- Oum–Seymour Definition 6.1 (p. 522): the cut-rank function
`cutrk_G(X) = cutrk*_G(X, V(G) \ X)`. -/
noncomputable def cutrk (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : ℤ :=
  cutrkStar G X Xᶜ

end ApproxCliqueWidth.Certificate
