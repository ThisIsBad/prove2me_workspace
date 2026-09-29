import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation

namespace EdmondsKarp.MaxCapacity

variable {V : Type} [Fintype V] [DecidableEq V]

/-- An augmenting path giving the maximum possible augmentation relative to `f` (§1.3, p. 253): an
augmenting path `P` whose `ε` is at least the `ε` of every augmenting path relative to `f`. -/
def IsMaxAugPath (N : Network V) (f : V → V → ℝ) (P : List V) : Prop :=
  IsAugPath N f P ∧ ∀ Q : List V, IsAugPath N f Q → pathEps N f Q ≤ pathEps N f P

/-- `K` steps of the labeling method with maximum augmentations (pp. 250, 253): `f 0` is a flow in
`N` and, for every `k < K`, `P k` is an augmenting path giving the maximum possible augmentation
relative to `f k`, and `f (k+1)` is obtained from `f k` by augmentation along `P k`. -/
def IsMaxAugRun (N : Network V) (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) : Prop :=
  IsFlow N (f 0) ∧
    ∀ k < K, IsMaxAugPath N (f k) (P k) ∧ f (k + 1) = augment N (f k) (P k)

/-- The number of arcs of `N` (the arcs of `A` together with the return arc `(t, s)`) with one end in
`X` and the other end outside `X` (§1.3, p. 253). -/
def crossArcCount (N : Network V) (X : Finset V) : ℕ :=
  (N.arcs.filter (fun p => (p.1 ∈ X ∧ p.2 ∉ X) ∨ (p.1 ∉ X ∧ p.2 ∈ X))).card

/-- The hypothesis on `M` of §1.3, p. 253: for any partition of the nodes into `X` and `X̄` with
`s ∈ X` and `t ∈ X̄`, the number of arcs of `N` with one end in `X` and the other in `X̄` is at
most `M`. -/
def CrossArcsBounded (N : Network V) (M : ℕ) : Prop :=
  ∀ X : Finset V, N.s ∈ X → N.t ∉ X → crossArcCount N X ≤ M

/-- `c(X, X̄) = Σ_{u ∈ X, v ∈ X̄, (u, v) ∈ A} c(u, v)` (proof of Theorem 2, p. 254). -/
def cutCap (N : Network V) (X : Finset V) : ℝ :=
  ∑ p ∈ N.A.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X), N.c p.1 p.2

/-- `f(X, X̄) = Σ_{u ∈ X, v ∈ X̄, (u, v) ∈ A} f(u, v)` (proof of Theorem 2, p. 254). -/
def cutFlowOut (N : Network V) (f : V → V → ℝ) (X : Finset V) : ℝ :=
  ∑ p ∈ N.A.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X), f p.1 p.2

/-- `f(X̄, X) = Σ_{u ∈ X̄, v ∈ X, (u, v) ∈ A} f(u, v)` (proof of Theorem 2, p. 254). -/
def cutFlowIn (N : Network V) (f : V → V → ℝ) (X : Finset V) : ℝ :=
  ∑ p ∈ N.A.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X), f p.1 p.2

end EdmondsKarp.MaxCapacity
