import Definitions.Def_CookLevin_Satisfiability

set_option autoImplicit false

namespace NPGraph

/-- Explicit graph data: `order` vertices numbered from zero and a row-major
Boolean adjacency matrix. `IsSimple` checks that these data describe a
finite simple undirected graph. -/
structure Graph where
  order : Nat
  bits : List Bool
  deriving DecidableEq, Repr

/-- Adjacency is false outside the declared vertex range. -/
def Adj (G : Graph) (u v : Nat) : Prop :=
  u < G.order ∧ v < G.order ∧
    G.bits.getD (u * G.order + v) false = true

/-- A complete square matrix with no self-loops and symmetric adjacency. -/
def IsSimple (G : Graph) : Prop :=
  G.bits.length = G.order * G.order ∧
  (∀ u < G.order, ¬ (NPGraph.Adj G) u u) ∧
  (∀ u < G.order, ∀ v < G.order, (NPGraph.Adj G) u v ↔ (NPGraph.Adj G) v u)

/-- Encode the vertex count, the input threshold, and the full adjacency
matrix. Both integers use Cook–Levin's self-delimiting unary encoding.
Well-formedness of the graph is checked separately by the decision language. -/
def encodeInstance (G : Graph) (k : Nat) : List Bool :=
  CookLevin.encodeNat G.order ++ CookLevin.encodeNat k ++ G.bits

end NPGraph
