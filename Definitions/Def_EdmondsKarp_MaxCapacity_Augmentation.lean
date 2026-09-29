import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network

namespace EdmondsKarp.MaxCapacity

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The arcs of the residual network `N^f` (§1.2, p. 251): `(u, v)` is an arc of `N^f` iff
`(u, v) ∈ A` and `c(u, v) − f(u, v) > 0`, or `(v, u) ∈ A` and `f(v, u) > 0`. -/
def ResArc (N : Network V) (f : V → V → ℝ) (u v : V) : Prop :=
  ((u, v) ∈ N.A ∧ 0 < N.c u v - f u v) ∨ ((v, u) ∈ N.A ∧ 0 < f v u)

/-- The consecutive pairs `(u_i, u_{i+1})` of a node sequence `u_1, …, u_p`. -/
def pathArcs (P : List V) : List (V × V) := P.zip P.tail

/-- A directed path from `u` to `v` in `N^f` (pp. 249, 251): a sequence of distinct nodes starting at
`u`, ending at `v`, each consecutive pair of which is an arc of `N^f`. Its length is the number of
arcs, `(pathArcs P).length`. -/
def IsDirPath (N : Network V) (f : V → V → ℝ) (u v : V) (P : List V) : Prop :=
  P.Nodup ∧ P.head? = some u ∧ P.getLast? = some v ∧ ∀ e ∈ pathArcs P, ResArc N f e.1 e.2

/-- An augmenting path relative to `f` (p. 249), encoded through the one-one correspondence of p. 251 as
a directed path from `s` to `t` in `N^f`. -/
def IsAugPath (N : Network V) (f : V → V → ℝ) (P : List V) : Prop :=
  IsDirPath N f N.s N.t P

/-- The number `ε_i` attached to a step `(u, v) = (u_i, u_{i+1})` of an augmenting path (p. 249,
Case (b) corrected to `(u, v) ∉ A`, `(v, u) ∈ A`):
(a) `(u,v) ∈ A`, `(v,u) ∉ A`: `c(u,v) − f(u,v)`; (b) `(u,v) ∉ A`, `(v,u) ∈ A`: `f(v,u)`;
(c) both in `A`: `c(u,v) − f(u,v) + f(v,u)`. (If neither is in `A` the value is irrelevant.)
On an arc `(u, v)` of `N^f` this is also the number `e(u, v)` of §1.3, p. 253, items (i)–(iii). -/
def stepEps (N : Network V) (f : V → V → ℝ) (u v : V) : ℝ :=
  if (u, v) ∈ N.A then
    (if (v, u) ∈ N.A then N.c u v - f u v + f v u else N.c u v - f u v)
  else f v u

/-- `ε = min ε_i` over the steps of the path `P` (p. 249). (The default `0` for a path without arcs
never arises for an augmenting path, which has at least one arc since `s ≠ t`.) -/
def pathEps (N : Network V) (f : V → V → ℝ) (P : List V) : ℝ :=
  (((pathArcs P).map (fun e => stepEps N f e.1 e.2)).min?).getD 0

/-- `(u, v)` is a bottleneck arc relative to `P` and `f` (pp. 249, 251): a step `(u_i, u_{i+1})` of `P`
(an arc of `N^f`) with `ε_i = ε`. -/
def IsBottleneck (N : Network V) (f : V → V → ℝ) (P : List V) (u v : V) : Prop :=
  (u, v) ∈ pathArcs P ∧ stepEps N f u v = pathEps N f P

/-- Increase of the flow on the arc `(x, y) ∈ A` in the augmentation along `P` (p. 249): `ε` in Case (a)
and `min(ε, c(x,y) − f(x,y))` in Case (c), when `(x, y)` is a step of `P`; otherwise `0`. -/
def augIncrease (N : Network V) (f : V → V → ℝ) (P : List V) (x y : V) : ℝ :=
  if (x, y) ∈ pathArcs P then
    (if (y, x) ∈ N.A then min (pathEps N f P) (N.c x y - f x y) else pathEps N f P)
  else 0

/-- Decrease of the flow on the arc `(x, y) ∈ A` in the augmentation along `P` (p. 249): when `(y, x)`
is a step of `P`, `ε` in Case (b) and `max(0, ε − c(y,x) + f(y,x))` in Case (c); otherwise `0`. -/
def augDecrease (N : Network V) (f : V → V → ℝ) (P : List V) (x y : V) : ℝ :=
  if (y, x) ∈ pathArcs P then
    (if (y, x) ∈ N.A then max 0 (pathEps N f P - N.c y x + f y x) else pathEps N f P)
  else 0

/-- The flow `f'` obtained from `f` by augmentation along `P` (p. 249): the return arc gains `ε`, each
arc of `A` changes by its increase minus its decrease; values off the arcs of `N` are left unchanged. -/
def augment (N : Network V) (f : V → V → ℝ) (P : List V) : V → V → ℝ :=
  fun x y =>
    if x = N.t ∧ y = N.s then f x y + pathEps N f P
    else if (x, y) ∈ N.A then f x y + augIncrease N f P x y - augDecrease N f P x y
    else f x y

end EdmondsKarp.MaxCapacity
