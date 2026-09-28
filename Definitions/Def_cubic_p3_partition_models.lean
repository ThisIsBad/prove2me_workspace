import Mathlib

namespace CubicP3Partition

universe u

variable {V : Type u} [Fintype V]

/-- The number of neighbors of a vertex. -/
noncomputable def degree (G : SimpleGraph V) (v : V) : Nat :=
  Nat.card {w : V // G.Adj v w}

/-- Every vertex has degree three. -/
def Cubic (G : SimpleGraph V) : Prop :=
  ∀ v, degree G v = 3

/-- Deleting any set of at most two vertices leaves a connected graph.
The order condition excludes the degenerate graphs with fewer than four vertices. -/
def ThreeVertexConnected (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card ≤ 2 →
      (G.induce {v : V | v ∉ S}).Connected

/-- A partition of the vertices into ordered triples whose first--second and
second--third pairs are edges. No condition is imposed on the ambient edge
between the first and third vertices, so these paths need not be induced. -/
structure P3Factor (G : SimpleGraph V) where
  blockCount : Nat
  place : (Fin blockCount × Fin 3) ≃ V
  edge01 : ∀ i : Fin blockCount, G.Adj (place (i, 0)) (place (i, 1))
  edge12 : ∀ i : Fin blockCount, G.Adj (place (i, 1)) (place (i, 2))

/-- A specified three-vertex path in the ambient graph. -/
structure P3Path (G : SimpleGraph V) where
  left : V
  center : V
  right : V
  left_ne_center : left ≠ center
  center_ne_right : center ≠ right
  left_ne_right : left ≠ right
  edge_left : G.Adj left center
  edge_right : G.Adj center right

/-- Delete the three vertices of a specified path and take the induced graph. -/
def eraseP3 (G : SimpleGraph V) (L : P3Path G) :
    SimpleGraph {v : V // v ≠ L.left ∧ v ≠ L.center ∧ v ≠ L.right} :=
  G.induce {v : V | v ≠ L.left ∧ v ≠ L.center ∧ v ≠ L.right}

/-- Claim (z1) in Kelmans's Theorem 3.1, restricted to ordinary small types. -/
def ClaimZ1 : Prop :=
  ∀ (W : Type) [Fintype W], ∀ G : SimpleGraph W,
    Cubic G → ThreeVertexConnected G → Fintype.card W % 6 = 0 →
      Nonempty (P3Factor G)

/-- Claim (z8) in Kelmans's Theorem 3.1, restricted to ordinary small types. -/
def ClaimZ8 : Prop :=
  ∀ (W : Type) [Fintype W], ∀ G : SimpleGraph W,
    Cubic G → ThreeVertexConnected G → Fintype.card W % 6 = 0 →
      ∀ L : P3Path G, Nonempty (P3Factor (eraseP3 G L))

/-- A spanning 2-regular subgraph. -/
def TwoFactor (G F : SimpleGraph V) : Prop :=
  F ≤ G ∧ ∀ v, degree F v = 2

/-- Number of vertices in the connected component of `v` in `F`. -/
noncomputable def componentOrder (F : SimpleGraph V) (v : V) : Nat :=
  Nat.card {w : V // F.Reachable v w}

/-- A spanning 2-factor all of whose connected components have order divisible by three. -/
def DivisibleTwoFactor (G F : SimpleGraph V) : Prop :=
  TwoFactor G F ∧ ∀ v, 3 ∣ componentOrder F v

/-- The graph has a divisible 2-factor. -/
def HasDivisibleTwoFactor (G : SimpleGraph V) : Prop :=
  ∃ F : SimpleGraph V, DivisibleTwoFactor G F

/-- A spanning 1-regular subgraph. -/
def PerfectMatching (G M : SimpleGraph V) : Prop :=
  M ≤ G ∧ ∀ v, degree M v = 1

/-- The relative edge complement of `M` inside `G`, on the same vertex type. -/
def matchingComplement (G M : SimpleGraph V) : SimpleGraph V :=
  G ⊓ Mᶜ

/-- The strengthened route: some perfect matching has a divisible 2-factor as its complement. -/
def HasDivisibleComplement (G : SimpleGraph V) : Prop :=
  ∃ M : SimpleGraph V,
    PerfectMatching G M ∧ DivisibleTwoFactor G (matchingComplement G M)

/-- The twelve internal edges of the fixed Petersen-minus-one-vertex brick. -/
def brickEdges : List (Nat × Nat) :=
  [(0, 1), (0, 5), (1, 2), (1, 6), (2, 3), (2, 7),
   (3, 8), (4, 6), (4, 7), (5, 7), (5, 8), (6, 8)]

/-- A directed presentation of the edges used to define the C02 family. -/
def forwardEdge (q u v : Nat) : Prop :=
  (u, v) ∈ brickEdges ∨
  (9 ≤ u ∧ (v = u + 1 ∨ v = u + (6 * q + 5))) ∨
  (u = 0 ∧ v = 9) ∨
  (u = 3 ∧ v = 17 + 12 * q) ∨
  (u = 4 ∧ v = 13 + 6 * q)

/-- The explicit C02 graph family, of order `18 + 12*q`. -/
def H (q : Nat) : SimpleGraph (Fin (18 + 12 * q)) where
  Adj u v := u ≠ v ∧
    (forwardEdge q u.val v.val ∨ forwardEdge q v.val u.val)
  symm := ⟨by
    intro u v h
    exact ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨by
    intro v h
    exact h.1 rfl⟩

end CubicP3Partition
