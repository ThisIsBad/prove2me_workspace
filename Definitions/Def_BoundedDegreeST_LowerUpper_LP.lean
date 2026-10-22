import Mathlib
import Definitions.Def_BoundedDegreeST_PlusOne_LP

namespace BoundedDegreeST.LowerUpper

/-- The supernode of `v`: the vertex set of the connected component of `v` in
the graph `(V, F)`, as a finite set (a singleton when `v` is isolated in `F`). -/
noncomputable def supernodeOf {V : Type*} [Fintype V] (F : Finset (Sym2 V)) (v : V) :
    Finset V := by
  classical
  exact Finset.univ.filter
    (fun w => (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable v w)

/-- `C(F)`: all supernodes of `F`, including singleton components. -/
noncomputable def supernodes {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Sym2 V)) : Finset (Finset V) :=
  Finset.univ.image (supernodeOf F)

/-- `S ∈ 𝓘(F)`: `S` is a union of supernodes, i.e. every component of `F`
lies inside `S` or is disjoint from `S`. -/
def Compatible {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Sym2 V)) (S : Finset V) : Prop :=
  ∀ C ∈ supernodes F, C ⊆ S ∨ Disjoint C S

/-- `E(S)` (or `F(S)`): the edges of `E` with both endpoints in `S`. -/
noncomputable def internal {V : Type*} (E : Finset (Sym2 V))
    (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => ∀ v ∈ e, v ∈ S)

/-- `δ_E(S)`: the edges of `E` with exactly one endpoint in `S`. -/
noncomputable def cut {V : Type*} (E : Finset (Sym2 V))
    (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => (∃ v ∈ e, v ∈ S) ∧ ∃ w ∈ e, w ∉ S)

/-- `deg_E(v)`: the number of edges of `E` incident to `v`. -/
noncomputable def degree {V : Type*} (E : Finset (Sym2 V)) (v : V) : ℕ := by
  classical
  exact (E.filter (fun e => v ∈ e)).card

/-- Feasibility for LP-MBDCT(G, 𝓐, 𝓑, U, W, F) (p. 668):
`x(E(V)) = |V| − |F(V)| − 1`, `x(E(S)) ≤ |S| − |F(S)| − 1` for nonempty
`S ∈ 𝓘(F)`, `x(δ(v)) ≥ A_v` on `U`, `x(δ(v)) ≤ B_v` on `W`, `x ≥ 0`.
Right-hand sides are computed in `ℝ`. -/
def Feasible {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  BoundedDegreeST.PlusOne.Supported E x ∧
  BoundedDegreeST.PlusOne.edgeSum x (internal E Finset.univ) =
    (Fintype.card V : ℝ) - ((internal F Finset.univ).card : ℝ) - 1 ∧
  (∀ S : Finset V, S.Nonempty → Compatible F S →
    BoundedDegreeST.PlusOne.edgeSum x (internal E S) ≤ (S.card : ℝ) - ((internal F S).card : ℝ) - 1) ∧
  (∀ v ∈ U, (A v : ℝ) ≤ BoundedDegreeST.PlusOne.edgeSum x (cut E {v})) ∧
  (∀ v ∈ W, BoundedDegreeST.PlusOne.edgeSum x (cut E {v}) ≤ (B v : ℝ)) ∧
  ∀ e ∈ E, 0 ≤ x e

/-- A basic feasible solution (p. 663): `x` is feasible and is the unique vector
supported on `E` satisfying with equality every constraint tight at `x`
(the equality row, the tight subtour rows, the tight lower- and upper-degree
rows, and the tight nonnegativity rows `x_e = 0`). -/
def Basic {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  Feasible E A B U W F x ∧
  ∀ y : Sym2 V → ℝ, BoundedDegreeST.PlusOne.Supported E y →
    BoundedDegreeST.PlusOne.edgeSum y (internal E Finset.univ) =
      (Fintype.card V : ℝ) - ((internal F Finset.univ).card : ℝ) - 1 →
    (∀ S : Finset V, S.Nonempty → Compatible F S →
      BoundedDegreeST.PlusOne.edgeSum x (internal E S) = (S.card : ℝ) - ((internal F S).card : ℝ) - 1 →
      BoundedDegreeST.PlusOne.edgeSum y (internal E S) = (S.card : ℝ) - ((internal F S).card : ℝ) - 1) →
    (∀ v ∈ U, BoundedDegreeST.PlusOne.edgeSum x (cut E {v}) = (A v : ℝ) →
      BoundedDegreeST.PlusOne.edgeSum y (cut E {v}) = (A v : ℝ)) →
    (∀ v ∈ W, BoundedDegreeST.PlusOne.edgeSum x (cut E {v}) = (B v : ℝ) →
      BoundedDegreeST.PlusOne.edgeSum y (cut E {v}) = (B v : ℝ)) →
    (∀ e ∈ E, x e = 0 → y e = 0) → y = x

/-- An optimal solution: feasible, with BoundedDegreeST.PlusOne.cost no larger than every feasible BoundedDegreeST.PlusOne.cost. -/
def Optimal {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) (E : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  Feasible E A B U W F x ∧
  ∀ y, Feasible E A B U W F y → ∑ e ∈ E, c e * x e ≤ ∑ e ∈ E, c e * y e

/-- The support `E* = {e ∈ E : x_e ≠ 0}`. -/
noncomputable def support {V : Type*}
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => x e ≠ 0)

/-- The characteristic vector `χ_D ∈ ℝ^{E*}` of an edge set `D`, indexed by the
support `E*` of `x`. -/
noncomputable def indicatorOnSupport {V : Type*}
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (D : Finset (Sym2 V)) : {e : Sym2 V // e ∈ support E x} → ℝ := by
  classical
  exact fun e => if e.val ∈ D then 1 else 0

/-- The conclusion of Lemma 5.3 (p. 668): `T_U ⊆ U`, `T_W ⊆ W` and a nonempty
laminar family `𝓛 ⊆ 𝓘(F)` of nonempty sets such that the rows
`x(δ(v)) = A_v` (`v ∈ T_U`), `x(δ(v)) = B_v` (`v ∈ T_W`),
`x(E(S)) = |S| − |F(S)| − 1` (`S ∈ 𝓛`) hold at `x`, `x` restricted to `E*` is
their unique solution in `ℝ^{E*}`, the vectors `χ_{E(S)}`, `χ_{δ(v)}`, `χ_{δ(v)}`
indexed by `𝓛 ⊕ T_U ⊕ T_W` are linearly independent in `ℝ^{E*}`, and
`|E*| = |𝓛| + |T_U| + |T_W|`. -/
def DefinesBasis {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (TU TW : Finset V) : Prop :=
  L.Nonempty ∧ BoundedDegreeST.PlusOne.Laminar L ∧
  (∀ S ∈ L, S.Nonempty ∧ Compatible F S) ∧ TU ⊆ U ∧ TW ⊆ W ∧
  (∀ v ∈ TU, BoundedDegreeST.PlusOne.edgeSum x (cut E {v}) = (A v : ℝ)) ∧
  (∀ v ∈ TW, BoundedDegreeST.PlusOne.edgeSum x (cut E {v}) = (B v : ℝ)) ∧
  (∀ S ∈ L, BoundedDegreeST.PlusOne.edgeSum x (internal E S) =
      (S.card : ℝ) - ((internal F S).card : ℝ) - 1) ∧
  (∀ y : {e : Sym2 V // e ∈ support E x} → ℝ,
    (∀ v ∈ TU, (∑ e, indicatorOnSupport E x (cut E {v}) e * y e) = (A v : ℝ)) →
    (∀ v ∈ TW, (∑ e, indicatorOnSupport E x (cut E {v}) e * y e) = (B v : ℝ)) →
    (∀ S ∈ L, (∑ e, indicatorOnSupport E x (internal E S) e * y e) =
      (S.card : ℝ) - ((internal F S).card : ℝ) - 1) →
    y = fun e => x e.val) ∧
  LinearIndependent ℝ
    (fun i : {S : Finset V // S ∈ L} ⊕ ({v : V // v ∈ TU} ⊕ {v : V // v ∈ TW}) =>
      match i with
      | .inl S => indicatorOnSupport E x (internal E S.val)
      | .inr (.inl v) => indicatorOnSupport E x (cut E {v.val})
      | .inr (.inr v) => indicatorOnSupport E x (cut E {v.val})) ∧
  (support E x).card = L.card + TU.card + TW.card

end BoundedDegreeST.LowerUpper
