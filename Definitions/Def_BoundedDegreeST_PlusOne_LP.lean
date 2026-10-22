import Mathlib

namespace BoundedDegreeST.PlusOne

/-- The graph is simple: loops are excluded from its finite edge set. -/
def SimpleEdges {V : Type*} (E : Finset (Sym2 V)) : Prop :=
  ∀ e ∈ E, ¬ e.IsDiag

/-- A forest on the full vertex set, including isolated vertices. -/
def IsForest {V : Type*} (F : Finset (Sym2 V)) : Prop :=
  SimpleEdges F ∧ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).IsAcyclic

/-- A spanning tree is connected and acyclic on the full vertex set. -/
def IsSpanningTree {V : Type*} (F : Finset (Sym2 V)) : Prop :=
  SimpleEdges F ∧ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).IsTree

/-- The vertex set of the component of `v` in `F`. -/
def component {V : Type*} (F : Finset (Sym2 V)) (v : V) : Set V :=
  {w | (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable v w}

/-- All components of `F`, including singleton components. -/
def components {V : Type*} (F : Finset (Sym2 V)) : Set (Set V) :=
  Set.range (component F)

/-- `S` is a union of components of `F`. -/
def Compatible {V : Type*} (F : Finset (Sym2 V)) (S : Finset V) : Prop :=
  ∀ C ∈ components F, C ⊆ (↑S : Set V) ∨ Disjoint C (↑S : Set V)

/-- `E(S)` or `F(S)`: edges with both endpoints in `S`. -/
noncomputable def internal {V : Type*} [DecidableEq V] (E : Finset (Sym2 V))
    (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => ∀ v ∈ e, v ∈ S)

/-- `δ_E(S)`: edges with exactly one endpoint in `S`. -/
noncomputable def cut {V : Type*} [DecidableEq V] (E : Finset (Sym2 V))
    (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => ∃ v ∈ e, v ∈ S ∧ ∃ w ∈ e, w ∉ S)

/-- Number of edges of `E` incident to `v`. -/
def degree {V : Type*} [DecidableEq V] (E : Finset (Sym2 V)) (v : V) : ℕ :=
  (E.filter (fun e => v ∈ e)).card

/-- The cost of an edge set. Costs need not be nonnegative. -/
def cost {V : Type*} (c : Sym2 V → ℝ) (E : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ E, c e

/-- The sum of a vector on an edge set. -/
def edgeSum {V : Type*} (x : Sym2 V → ℝ) (E : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ E, x e

/-- Vectors have variables only on the current graph's edges. -/
def Supported {V : Type*} (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  ∀ e, e ∉ E → x e = 0

/-- Feasibility for LP-MBDCT, equations (16)–(19). The subtour rows range over
nonempty component unions, since the literal empty-set row would be impossible. -/
def Feasible {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (B : V → ℤ) (W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  Supported E x ∧
  edgeSum x E = (Fintype.card V : ℝ) - (F.card : ℝ) - 1 ∧
  (∀ S : Finset V, S.Nonempty → Compatible F S →
    edgeSum x (internal E S) ≤ (S.card : ℝ) - ((internal F S).card : ℝ) - 1) ∧
  (∀ v ∈ W, edgeSum x (cut E {v}) ≤ (B v : ℝ)) ∧
  ∀ e ∈ E, 0 ≤ x e

/-- The tight equations determine `x` uniquely in the current edge-variable
space. This includes the tight nonnegativity rows. -/
def Basic {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (B : V → ℤ) (W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  Feasible E B W F x ∧
  ∀ y : Sym2 V → ℝ, Supported E y →
    edgeSum y E = (Fintype.card V : ℝ) - (F.card : ℝ) - 1 →
    (∀ S : Finset V, S.Nonempty → Compatible F S →
      edgeSum x (internal E S) = (S.card : ℝ) - ((internal F S).card : ℝ) - 1 →
      edgeSum y (internal E S) = (S.card : ℝ) - ((internal F S).card : ℝ) - 1) →
    (∀ v ∈ W, edgeSum x (cut E {v}) = (B v : ℝ) →
      edgeSum y (cut E {v}) = (B v : ℝ)) →
    (∀ e ∈ E, x e = 0 → y e = 0) → y = x

/-- A feasible vector whose cost is no larger than every feasible cost. -/
def Optimal {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) (E : Finset (Sym2 V)) (B : V → ℤ)
    (W : Finset V) (F : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  Feasible E B W F x ∧
  ∀ y, Feasible E B W F y → ∑ e ∈ E, c e * x e ≤ ∑ e ∈ E, c e * y e

/-- The positive support of a feasible vector. -/
noncomputable def support {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => x e ≠ 0)

/-- Intersecting vertex sets cross in all three regions. -/
def Intersecting {V : Type*} [DecidableEq V]
    (S T : Finset V) : Prop :=
  (S ∩ T).Nonempty ∧ (S \ T).Nonempty ∧ (T \ S).Nonempty

/-- A family with no intersecting pair. -/
def Laminar {V : Type*} [DecidableEq V]
    (L : Finset (Finset V)) : Prop :=
  ∀ S ∈ L, ∀ T ∈ L, ¬ Intersecting S T

/-- The vector indexed by the support of `x` for an edge indicator. -/
def indicatorOnSupport {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (A : Finset (Sym2 V)) : {e : Sym2 V // e ∈ support E x} → ℝ :=
  fun e => if e.val ∈ A then 1 else 0

/-- The tight laminar rows and degree rows form a basis on the support, and
uniquely determine the positive variables. -/
def DefinesBasis {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (B : V → ℤ) (W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) : Prop :=
  L.Nonempty ∧ Laminar L ∧
  (∀ S ∈ L, S.Nonempty ∧ Compatible F S) ∧ T ⊆ W ∧
  (∀ S ∈ L, edgeSum x (internal E S) =
      (S.card : ℝ) - ((internal F S).card : ℝ) - 1) ∧
  (∀ v ∈ T, edgeSum x (cut E {v}) = (B v : ℝ)) ∧
  (∀ y : {e : Sym2 V // e ∈ support E x} → ℝ,
    (∀ S ∈ L, (∑ e, if e.val ∈ internal E S then y e else 0) =
      (S.card : ℝ) - ((internal F S).card : ℝ) - 1) →
    (∀ v ∈ T, (∑ e, if e.val ∈ cut E {v} then y e else 0) = (B v : ℝ)) →
    y = fun e => x e.val) ∧
  LinearIndependent ℝ (fun i : Sum {S : Finset V // S ∈ L} {v : V // v ∈ T} =>
    match i with
    | .inl S => indicatorOnSupport E x (internal E S.val)
    | .inr v => indicatorOnSupport E x (cut E {v.val})) ∧
  (support E x).card = L.card + T.card

/-- Excess vertex tokens after reserving two for each vertex in `T`. -/
def excessTokens {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (T : Finset V) (v : V) : ℤ :=
  (degree E v : ℤ) - (if v ∈ T then 2 else 0)

end BoundedDegreeST.PlusOne
