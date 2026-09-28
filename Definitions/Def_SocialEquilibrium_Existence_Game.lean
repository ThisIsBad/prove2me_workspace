import Mathlib

namespace SocialEquilibrium.Existence

open Filter Topology

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*}

/-- Debreu (1952), §2, p. 888: given the action sets `𝔄_j = X j`, the set `𝔄̄_ι` of
`(ν − 1)`-tuples `ā_ι = (a_1, …, a_{ι−1}, a_{ι+1}, …, a_ν)` of actions of all agents other
than `ι`. -/
abbrev Others (X : ∀ i, Set (E i)) (i : ι) : Type _ :=
  ∀ j : {j // j ≠ i}, X j

/-- The actions `ā_ι` of all agents other than `ι` in the profile `a`. -/
def others (X : ∀ i, Set (E i)) (i : ι) (a : ∀ j, X j) : Others X i :=
  fun j => a j

/-- The profile `(ā_ι, a_ι)` obtained by joining the others' actions `ā_ι` with the action
`b = a_ι` of agent `ι`. -/
def join (X : ∀ i, Set (E i)) (i : ι) (ā : Others X i) (b : X i) : ∀ j, X j :=
  (Equiv.piSplitAt i (fun j => (X j : Type _))).symm (b, ā)

/-- Debreu (1952), §2, p. 888: `φ_ι(ā_ι) = Max_{a_ι ∈ A_ι(ā_ι)} f_ι(ā_ι, a_ι)`, the best payoff
available to agent `ι` when the others play `ā_ι`, written as a supremum in the completed real
line `EReal` (a complete lattice). -/
noncomputable def bestValue (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) (ā : Others X i) : EReal :=
  sSup ((fun b => f i (join X i ā b)) '' A i ā)

/-- Debreu (1952), §2, p. 888: `M_{ā_ι} = {a_ι ∈ A_ι(ā_ι) | f_ι(ā_ι, a_ι) = φ_ι(ā_ι)}`, the set
of constrained best responses of agent `ι` to `ā_ι`. -/
def bestSet (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (i : ι) (ā : Others X i) : Set (X i) :=
  {b | b ∈ A i ā ∧ f i (join X i ā b) = bestValue X A f i ā}

/-- Debreu (1952), §2, p. 889: the multi-valued function `φ(a) = M_{ā_1} × ⋯ × M_{ā_ν}` on the
set of profiles `𝔄`. -/
def bestResponse (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (a : ∀ j, X j) : Set (∀ j, X j) :=
  {a' | ∀ i, a' i ∈ bestSet X A f i (others X i a)}

/-- Debreu (1952), §2, p. 888, Definition: `a*` is an *equilibrium point* if for every agent
`ι`, `a*_ι ∈ A_ι(ā*_ι)` and `f_ι(a*)` is the maximum of `f_ι(ā*_ι, a_ι)` over
`a_ι ∈ A_ι(ā*_ι)`. -/
def IsEquilibrium (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (a : ∀ j, X j) : Prop :=
  ∀ i, a i ∈ A i (others X i a) ∧
    ∀ b ∈ A i (others X i a), f i (join X i (others X i a) b) ≤ f i a

/-- Debreu (1952), §2, p. 889: the multi-valued function `A_ι` is *continuous* at `ā⁰_ι` if for
any `a⁰_ι ∈ A_ι(ā⁰_ι)` and any sequence `(āⁿ_ι)` converging to `ā⁰_ι` there is a sequence
`(aⁿ_ι)` converging to `a⁰_ι` with `aⁿ_ι ∈ A_ι(āⁿ_ι)` for all `n`. -/
def ConstraintContinuousAt {X : ∀ i, Set (E i)} [∀ i, TopologicalSpace (E i)]
    (A : ∀ i : ι, Others X i → Set (X i)) (i : ι) (ā₀ : Others X i) : Prop :=
  ∀ a₀ ∈ A i ā₀, ∀ ā : ℕ → Others X i, Tendsto ā atTop (𝓝 ā₀) →
    ∃ a : ℕ → X i, Tendsto a atTop (𝓝 a₀) ∧ ∀ n, a n ∈ A i (ā n)

end SocialEquilibrium.Existence
