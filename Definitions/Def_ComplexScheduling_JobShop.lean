import Mathlib

namespace ComplexScheduling

variable {N : ℕ} {M : Type*}

/-- The arc relation of a finite set of directed arcs. -/
def ArcRel (A : Finset (Fin N × Fin N)) : Fin N → Fin N → Prop := fun i j => (i, j) ∈ A

/-- A directed arc set is **acyclic** when no vertex reaches itself along a nonempty path.
Brucker and Knust, *Complex Scheduling*, §4.1.2, p. 241. -/
def AcyclicArcs (A : Finset (Fin N × Fin N)) : Prop :=
  ∀ i : Fin N, ¬ Relation.TransGen (ArcRel A) i i

/-- A **complete selection** for the disjunction set `D`: for each undirected disjunction
`i - j`, listed in `D` as the pair `(i, j)`, exactly one of the two orientations is fixed in `S`,
and `S` fixes nothing else.  Brucker and Knust §4.1.2, p. 241. -/
def CompleteSelection (D S : Finset (Fin N × Fin N)) : Prop :=
  (∀ e ∈ S, e ∈ D ∨ (e.2, e.1) ∈ D) ∧
    ∀ e ∈ D, (e ∈ S ∧ (e.2, e.1) ∉ S) ∨ (e ∉ S ∧ (e.2, e.1) ∈ S)

/-- A complete selection is **consistent** when `G(S) = (V, C ∪ S)` is acyclic.  Brucker and
Knust §4.1.2, p. 241. -/
def ConsistentSelection (Cn D S : Finset (Fin N × Fin N)) : Prop :=
  CompleteSelection D S ∧ AcyclicArcs (Cn ∪ S)

/-- A schedule **respects** an arc set when every arc `i → j` gives `S i + p i ≤ S j`. -/
def RespectsArcs (p : Fin N → ℕ) (A : Finset (Fin N × Fin N)) (St : Fin N → ℕ) : Prop :=
  ∀ e ∈ A, St e.1 + p e.1 ≤ St e.2

/-- `St` is **the earliest start schedule** of the arc set `A`: it respects `A` and starts every
operation no later than any schedule that respects `A`.  This is the schedule `S_i := r_i` of
Brucker and Knust §4.1.2, p. 241, where `r_i` is the length of a longest path from `0` to `i`. -/
def IsEarliestStart (p : Fin N → ℕ) (A : Finset (Fin N × Fin N)) (St : Fin N → ℕ) : Prop :=
  RespectsArcs p A St ∧ ∀ St' : Fin N → ℕ, RespectsArcs p A St' → ∀ i, St i ≤ St' i

/-- A list of vertices is a **path** of the arc set `A` when consecutive entries are joined by
arcs.  The empty list is not a path. -/
def IsPath (A : Finset (Fin N × Fin N)) : List (Fin N) → Prop
  | [] => False
  | [_] => True
  | a :: b :: t => (a, b) ∈ A ∧ IsPath A (b :: t)

/-- The **length of a path**: the sum of the weights of all its vertices, the last excluded.
Brucker and Knust §4.1.2, p. 241. -/
def pathLength (p : Fin N → ℕ) (l : List (Fin N)) : ℕ := (l.dropLast.map p).sum

/-- A **critical path** of `G(S)`: a longest path from the initial dummy operation `src` to the
terminal dummy operation `snk`.  Its length is the makespan.  Brucker and Knust §4.1.2, p. 241
and §4.2, p. 243. -/
def IsCriticalPath (p : Fin N → ℕ) (A : Finset (Fin N × Fin N)) (src snk : Fin N)
    (l : List (Fin N)) : Prop :=
  IsPath A l ∧ l.head? = some src ∧ l.getLast? = some snk ∧
    ∀ l' : List (Fin N), IsPath A l' → l'.head? = some src → l'.getLast? = some snk →
      pathLength p l' ≤ pathLength p l

/-- A **machine block** of the critical path `path`: a contiguous stretch `B` of at least two
operations, all on the same machine, that cannot be extended at either end without leaving that
machine.  The surrounding stretches `pre` and `post` witness the position of `B` in the path, and
`pre.reverse.take 1` and `post.take 1` are the single neighbouring operations, if any.
Brucker and Knust §4.2, p. 245. -/
def IsBlock (μ : Fin N → M) (path pre B post : List (Fin N)) : Prop :=
  path = pre ++ B ++ post ∧ 2 ≤ B.length ∧
    (∀ x ∈ B, ∀ y ∈ B, μ x = μ y) ∧
    (∀ x ∈ pre.reverse.take 1, ∀ y ∈ B, μ x ≠ μ y) ∧
    (∀ x ∈ post.take 1, ∀ y ∈ B, μ x ≠ μ y)

/-- An arc of the selection `S` lying on the critical path — that is, a pair of operations
adjacent on the path: the **critical arcs**, whose reversal generates the neighbourhood `N_ca`.
Brucker and Knust §4.2, p. 244. -/
def IsCriticalArc (S : Finset (Fin N × Fin N)) (l : List (Fin N)) (e : Fin N × Fin N) : Prop :=
  e ∈ S ∧ e ∈ l.zip l.tail

/-- The selection obtained from `S` by reversing the arc `e`. -/
def reverseArc (S : Finset (Fin N × Fin N)) (e : Fin N × Fin N) : Finset (Fin N × Fin N) :=
  insert (e.2, e.1) (S.erase e)

/-- `S'` is a neighbour of `S` in the **critical-arc neighbourhood** `N_ca`: it is obtained from
`S` by reversing a single arc of `S` lying on a critical path of `G(S)`.  Brucker and Knust
§4.2, p. 244. -/
def NcaNeighbour (p : Fin N → ℕ) (Cn : Finset (Fin N × Fin N)) (src snk : Fin N)
    (S S' : Finset (Fin N × Fin N)) : Prop :=
  ∃ (l : List (Fin N)) (e : Fin N × Fin N),
    IsCriticalPath p (Cn ∪ S) src snk l ∧ IsCriticalArc S l e ∧ S' = reverseArc S e

/-- A complete consistent selection is **optimal** when no complete consistent selection has a
shorter critical path, that is, a smaller makespan.  Brucker and Knust §4.1.2, p. 241. -/
def IsOptimalSelection (p : Fin N → ℕ) (Cn D : Finset (Fin N × Fin N)) (src snk : Fin N)
    (S : Finset (Fin N × Fin N)) : Prop :=
  ConsistentSelection Cn D S ∧
    ∀ (T : Finset (Fin N × Fin N)) (l lT : List (Fin N)), ConsistentSelection Cn D T →
      IsCriticalPath p (Cn ∪ S) src snk l → IsCriticalPath p (Cn ∪ T) src snk lT →
        pathLength p l ≤ pathLength p lT

end ComplexScheduling
