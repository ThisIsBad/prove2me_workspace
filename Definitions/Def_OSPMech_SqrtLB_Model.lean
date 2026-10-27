import Mathlib

namespace OSPMech.SqrtLB

/-- §2, pp. 6–7: an implementation tree 𝒯 for `n` agents with outcomes in `X`.
An internal vertex `u` is labelled by an agent `i = S(u)` and an action map `act : ℝ → ℕ`: a profile `b`
leaves `u` towards the child `act (b i)`. The edge label T(u, v) is the set of profiles compatible with
`u` whose action selects `v`. Because `act` is a function of the agent's own type, the four conditions
on edge labels of p. 7 hold automatically (outgoing labels are disjoint, they cover the incoming label,
the root's cover every profile, and the child chosen depends on `bᵢ` only). Every leaf `ℓ` carries an
outcome `X(ℓ)`. Root-to-leaf paths are finite. -/
inductive ImplTree (n : ℕ) (X : Type) where
  | leaf : X → ImplTree n X
  | node : Fin n → (ℝ → ℕ) → (ℕ → ImplTree n X) → ImplTree n X

variable {n : ℕ} {X : Type}

/-- p. 7: ℳ(b) = X(ℓ(b)), the outcome at the unique leaf reached by the profile `b`. -/
def outcome : ImplTree n X → (Fin n → ℝ) → X
  | .leaf x, _ => x
  | .node i act ch, b => outcome (ch (act (b i))) b

/-- The list of child indices that the profile `b` follows from the root to its leaf. -/
def path : ImplTree n X → (Fin n → ℝ) → List ℕ
  | .leaf _, _ => []
  | .node i act ch, b => act (b i) :: path (ch (act (b i))) b

/-- The vertex at position `pos` (a list of child indices read from the root), if it exists. -/
def subtreeAt : ImplTree n X → List ℕ → Option (ImplTree n X)
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .node _ _ ch, k :: pos => subtreeAt (ch k) pos

/-- p. 7: the profile `b` is compatible with the vertex at position `pos`, i.e. `b ∈ T(φ(u), u)`:
the path of `b` passes through that vertex. -/
def Compatible (t : ImplTree n X) (pos : List ℕ) (b : Fin n → ℝ) : Prop := pos <+: path t b

/-- `b ∈ D = ×ᵢ Dᵢ`. -/
def InDomain (D : Fin n → Finset ℝ) (b : Fin n → ℝ) : Prop := ∀ i, b i ∈ D i

/-- p. 7: the vertex at position `pos` is labelled by agent `i`, the profiles `b` and `b'` are both
compatible with it, and they diverge there (they leave it through different children). -/
def DivergeAt (t : ImplTree n X) (pos : List ℕ) (i : Fin n) (b b' : Fin n → ℝ) : Prop :=
  Compatible t pos b ∧ Compatible t pos b' ∧
    ∃ act ch, subtreeAt t pos = some (.node i act ch) ∧ act (b i) ≠ act (b' i)

/-- p. 7: obvious strategyproofness of the extensive-form mechanism with tree `t` and payments `p`,
where `cost i a x` is the cost a(x) of agent `i` of type `a` for the outcome `x`. For every vertex
labelled `i`, every true profile `b = (tᵢ, b₋ᵢ)` and every deviation `bDev = (bᵢ, b′₋ᵢ)` in `D` that are
compatible with the vertex and diverge there (so `bᵢ ≠ tᵢ`), the utility of truth-telling is at least
that of deviating: uᵢ(tᵢ, ℳ(tᵢ, b₋ᵢ)) ≥ uᵢ(tᵢ, ℳ(bᵢ, b′₋ᵢ)), with uᵢ(tᵢ, ℳ(b)) = pᵢ(b) − tᵢ(f(b)).
Payments are a function of the declared profile, p = p(b) (p. 6). -/
def IsOSP (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ) (t : ImplTree n X)
    (p : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ (pos : List ℕ) (i : Fin n) (b bDev : Fin n → ℝ), InDomain D b → InDomain D bDev →
    DivergeAt t pos i b bDev →
    p bDev i - cost i (b i) (outcome t bDev) ≤ p b i - cost i (b i) (outcome t b)

/-- Definition 2, p. 8: an edge of the OSP-graph 𝒪ᵢ^𝒯 from the profile `a = (a, a₋ᵢ)` to the profile
`b = (b, b₋ᵢ)`: both in `D`, and both compatible with some `ab`-separating vertex `u` for `i` (a vertex
labelled `i` where they diverge). -/
def OSPEdge (D : Fin n → Finset ℝ) (t : ImplTree n X) (i : Fin n) (a b : Fin n → ℝ) : Prop :=
  InDomain D a ∧ InDomain D b ∧ ∃ pos, DivergeAt t pos i a b

/-- The weight of the OSP-graph edge from `a` to `b`: aᵢ(f(b)) − aᵢ(f(a)), the cost for type `aᵢ` of the
outcome at the head minus its cost of the outcome at the tail (the weight of Observation 1, (1), and of
the proof of Theorem 3, p. 24; Definition 2 prints the opponents' profiles swapped). -/
def edgeWeight (cost : Fin n → ℝ → X → ℝ) (t : ImplTree n X) (i : Fin n) (a b : Fin n → ℝ) : ℝ :=
  cost i (a i) (outcome t b) - cost i (a i) (outcome t a)

/-- 𝒪ᵢ^𝒯 has no negative-weight cycle: every closed walk `w 0 → w 1 → ⋯ → w k → w 0` along its edges
has non-negative total weight. -/
def NoNegCycle (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ) (t : ImplTree n X) (i : Fin n) :
    Prop :=
  ∀ (k : ℕ) (w : Fin (k + 1) → (Fin n → ℝ)),
    (∀ j, OSPEdge D t i (w j) (w (finRotate (k + 1) j))) →
    0 ≤ ∑ j, edgeWeight cost t i (w j) (w (finRotate (k + 1) j))

/-! Machine scheduling, p. 8: `m` identical jobs on related machines; an outcome is the vector of job
loads `x : Fin n → ℕ`. -/

/-- The cost tᵢ · fᵢ of agent `i` of type `a` for the load vector `x`. -/
def schedCost : Fin n → ℝ → (Fin n → ℕ) → ℝ := fun i a x => a * x i

/-- The makespan maxᵢ bᵢ xᵢ of the load vector `x` under the processing times `b`. -/
noncomputable def makespan (b : Fin n → ℝ) (x : Fin n → ℕ) : ℝ := ⨆ i, b i * (x i : ℝ)

/-- OPT(b): the least makespan over all schedules of the `m` identical jobs. -/
noncomputable def optMakespan (m : ℕ) (b : Fin n → ℝ) : ℝ :=
  sInf ((fun x => makespan b x) '' {x : Fin n → ℕ | ∑ i, x i = m})

/-- Every outcome of the tree on a profile of `D` schedules exactly the `m` jobs. -/
def IsSchedule (m : ℕ) (D : Fin n → Finset ℝ) (t : ImplTree n (Fin n → ℕ)) : Prop :=
  ∀ b, InDomain D b → ∑ i, outcome t b i = m

/-- p. 8: the mechanism is `k`-approximate on `D`: its makespan is at most `k` times the optimum on
every profile of `D`. -/
def IsKApprox (m : ℕ) (k : ℝ) (D : Fin n → Finset ℝ) (t : ImplTree n (Fin n → ℕ)) : Prop :=
  ∀ b, InDomain D b → makespan b (outcome t b) ≤ k * optMakespan m b

/-! The renaming of the agents in the proof of Theorem 12, p. 12. -/

/-- The vertex at position `pos` is a divergent node with divergent agent `i` (p. 7): it is labelled
by `i` and two profiles of `D` diverge there. -/
def IsDivergentNode (D : Fin n → Finset ℝ) (t : ImplTree n X) (pos : List ℕ) (i : Fin n) : Prop :=
  ∃ b b', InDomain D b ∧ InDomain D b' ∧ DivergeAt t pos i b b'

/-- p. 12: agent `i` is the (r + 1)-th agent to diverge in the subtree in which every agent that
previously diverged took the action compatible with type `H`, and `pos` is the node uᵢ at which `i`
diverges there. That subtree is followed exactly by the all-`H` profile: on its path, a vertex labelled
by an agent that has not diverged before either is not divergent (all compatible profiles take the same
child) or is that agent's divergence. So: `pos` lies on the path of the all-`H` profile, `i` diverges at
`pos` and at no earlier vertex of that path, and exactly `r` distinct agents diverge at earlier vertices
of that path. The rank `r` is 0-based: the paper's agent `i` has `r = i − 1`. -/
def IsKthDiverger (D : Fin n → Finset ℝ) (t : ImplTree n X) (H : ℝ) (r : ℕ) (i : Fin n)
    (pos : List ℕ) : Prop :=
  pos <+: path t (fun _ => H) ∧ IsDivergentNode D t pos i ∧
    (∀ pos', pos' <+: pos → pos' ≠ pos → ¬ IsDivergentNode D t pos' i) ∧
    {j : Fin n | ∃ pos', pos' <+: pos ∧ pos' ≠ pos ∧ IsDivergentNode D t pos' j}.ncard = r

end OSPMech.SqrtLB
