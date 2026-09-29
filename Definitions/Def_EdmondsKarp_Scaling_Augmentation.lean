import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport

namespace EdmondsKarp.Scaling

variable {m n : ℕ}

/-- The quantity `ε_i` of §1.1 (p. 249) for a consecutive pair `(u, v)` of a path, in the network of
Figure 1 (no two arcs of `A` are antiparallel, so only Cases (a) and (b) occur):
Case (a), `(u, v) ∈ A`: `c(u, v) - f(u, v)` — this is `+∞` on the infinite-capacity arcs `(s_i, t_j)`;
Case (b), `(v, u) ∈ A`: `f(v, u)`.
Every other pair (including the return arc `(t, s)` in either direction) gets `0`, i.e. is not
usable in an augmenting path. -/
def resCap (T : Transport m n) (x : Flow m n) : Node m n → Node m n → WithTop ℝ
  | .s, .src i => ((T.a i - x.f0 i : ℝ) : WithTop ℝ)
  | .src _, .dst _ => ⊤
  | .dst j, .t => ((T.b j - x.fz j : ℝ) : WithTop ℝ)
  | .src i, .s => ((x.f0 i : ℝ) : WithTop ℝ)
  | .dst j, .src i => ((x.fx i j : ℝ) : WithTop ℝ)
  | .t, .dst j => ((x.fz j : ℝ) : WithTop ℝ)
  | _, _ => 0

/-- An augmenting path relative to `x` (§1.1, p. 249): a list `u_1 = s, …, u_p = t` of distinct
nodes such that every consecutive pair `(u_i, u_{i+1})` has `ε_i > 0`. -/
def IsAugPath (T : Transport m n) (x : Flow m n) (L : List (Node m n)) : Prop :=
  L.Nodup ∧ L.head? = some .s ∧ L.getLast? = some .t ∧
    ∀ e ∈ L.zip L.tail, 0 < resCap T x e.1 e.2

/-- `ε = min ε_i` over the consecutive pairs of the path `L` (§1.1, p. 249); `ε` is a real number
attained at some pair (a bottleneck arc). -/
def IsPathMin (T : Transport m n) (x : Flow m n) (L : List (Node m n)) (ε : ℝ) : Prop :=
  (∀ e ∈ L.zip L.tail, (ε : WithTop ℝ) ≤ resCap T x e.1 e.2) ∧
    ∃ e ∈ L.zip L.tail, resCap T x e.1 e.2 = (ε : WithTop ℝ)

/-- `+1` if `(u, v)` is traversed forward by the path `L` (a consecutive pair `u, v`), `-1` if it
is traversed in reverse (a consecutive pair `v, u`), `0` otherwise. -/
def pathDir (L : List (Node m n)) (u v : Node m n) : ℝ :=
  (if (u, v) ∈ L.zip L.tail then 1 else 0) - (if (v, u) ∈ L.zip L.tail then 1 else 0)

/-- The augmentation of §1.1 (p. 249) along `L` by `ε`: increase the return arc by `ε`; on each arc
of `A`, increase the flow by `ε` if the path uses it as a forward arc (Case (a)) and decrease it by
`ε` if the path uses it as a reverse arc (Case (b)). -/
def augment (x : Flow m n) (L : List (Node m n)) (ε : ℝ) : Flow m n where
  f0 i := x.f0 i + ε * pathDir L .s (.src i)
  fx i j := x.fx i j + ε * pathDir L (.src i) (.dst j)
  fz j := x.fz j + ε * pathDir L (.dst j) .t
  ret := x.ret + ε

/-- One flow augmentation: `y` is obtained from `x` by augmenting along some augmenting path relative
to `x` by its minimum `ε`. -/
def AugStep (T : Transport m n) (x y : Flow m n) : Prop :=
  ∃ (L : List (Node m n)) (ε : ℝ), IsAugPath T x L ∧ IsPathMin T x L ε ∧ y = augment x L ε

end EdmondsKarp.Scaling
