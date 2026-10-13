import Mathlib

namespace OnlineStochMatching.Hardness

/-- The advertisers `A = {a, b, c}` of the 6-cycle instance (§3, p. 4). -/
inductive Adv
  | a
  | b
  | c
  deriving DecidableEq, Repr

instance : Fintype Adv := ⟨{.a, .b, .c}, fun p => by cases p <;> decide⟩

/-- The impression types `I = {x, y, z}` of the 6-cycle instance (§3, p. 4). -/
inductive Imp
  | x
  | y
  | z
  deriving DecidableEq, Repr

instance : Fintype Imp := ⟨{.x, .y, .z}, fun i => by cases i <;> decide⟩

/-- The edge set `E = {(x, a), (y, a), (y, b), (z, b), (z, c), (x, c)}` of the 6-cycle (§3, p. 4),
written as (advertiser, impression type) pairs. -/
def cycleEdges : Finset (Adv × Imp) :=
  {(.a, .x), (.a, .y), (.b, .y), (.b, .z), (.c, .z), (.c, .x)}

/-- Adjacency in the 6-cycle: `cycleEdge p i` iff `(p, i) ∈ E`. -/
def cycleEdge (p : Adv) (i : Imp) : Prop := (p, i) ∈ cycleEdges

instance : DecidableRel cycleEdge := fun p i => by
  unfold cycleEdge
  infer_instance

/-- The `k` disjoint copies of the 6-cycle (App. B, p. 13): advertisers `Fin k × A`, impression
types `Fin k × I`, and `((j, p), (j', i))` is an edge iff the two lie in the same copy (`j = j'`)
and `(p, i)` is an edge of the 6-cycle. -/
def kCycleEdge (k : ℕ) (p : Fin k × Adv) (i : Fin k × Imp) : Prop :=
  p.1 = i.1 ∧ cycleEdge p.2 i.2

instance (k : ℕ) : DecidableRel (kCycleEdge k) := fun p i => by
  unfold kCycleEdge
  infer_instance

end OnlineStochMatching.Hardness
