import Mathlib

namespace SecretaryWD.Graphic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite edge set `S` is independent in the graphic matroid (p. 9): the graph on `V` with
edge set `S` contains no cycle. -/
def IsAcyclicSet (S : Finset (Sym2 V)) : Prop :=
  (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).IsAcyclic

theorem isAcyclicSet_empty : IsAcyclicSet (∅ : Finset (Sym2 V)) := by
  simp [IsAcyclicSet, SimpleGraph.isAcyclic_bot]

open Classical in
/-- The independent sets of the graphic matroid on the edge set `E`: the acyclic subsets of `E`. -/
noncomputable def acyclicSubsets (E : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) :=
  E.powerset.filter IsAcyclicSet

theorem empty_mem_acyclicSubsets (E : Finset (Sym2 V)) : ∅ ∈ acyclicSubsets E := by
  classical
  simp only [acyclicSubsets, Finset.mem_filter, Finset.empty_mem_powerset, true_and]
  exact isAcyclicSet_empty

/-- `OPT(G)`: the value of a max-weight independent set of the graphic matroid on `E`,
`max { ∑_{e ∈ S} v e : S ⊆ E acyclic }` (the maximum exists: `∅` is acyclic). -/
noncomputable def OPT (E : Finset (Sym2 V)) (v : Sym2 V → ℝ) : ℝ :=
  (acyclicSubsets E).sup' ⟨∅, empty_mem_acyclicSubsets E⟩ fun S => ∑ e ∈ S, v e

/-- `P` is a partition matroid on a subset `U' = ⋃ P` of the ground set `E` (p. 9): a finite
family of nonempty, pairwise disjoint parts, each contained in `E`. -/
def IsPartitionOf (E : Finset (Sym2 V)) (P : Finset (Finset (Sym2 V))) : Prop :=
  (∀ p ∈ P, p.Nonempty ∧ p ⊆ E) ∧ (P : Set (Finset (Sym2 V))).PairwiseDisjoint id

/-- `S` is independent in the partition matroid with parts `P` (p. 9): every element of `S`
lies in some part (so `S ⊆ U'`), and `S` has at most one element from each part. -/
def IsPartIndep (P : Finset (Finset (Sym2 V))) (S : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ S, ∃ p ∈ P, e ∈ p) ∧ ∀ p ∈ P, (S ∩ p).card ≤ 1

/-- The largest value in a part (`0` on an empty part, which never occurs in a partition). -/
noncomputable def partMax (p : Finset (Sym2 V)) (v : Sym2 V → ℝ) : ℝ :=
  if h : p.Nonempty then p.sup' h v else 0

/-- The value of a max-weight base of the partition matroid with parts `P`, for nonnegative
values: the sum over the parts of the largest value in the part. -/
noncomputable def partitionValue (P : Finset (Finset (Sym2 V))) (v : Sym2 V → ℝ) : ℝ :=
  ∑ p ∈ P, partMax p v

/-- The expectation of a real function `f` under a probability mass function `μ` on a finite
type: `∑_a μ(a) · f(a)`. -/
noncomputable def pmfExp {α : Type*} [Fintype α] (μ : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (μ a).toReal * f a

/-- Definition 5.1 for the graphic matroid on `E`, for a given random partition `μ`: the law `μ`
is fixed first (it may depend on `E` only), and then
* every partition `P` in the support of `μ` is a partition matroid on a subset of `E` whose
  independent sets are all independent (acyclic) in the graphic matroid, and
* for **every** nonnegative valuation `v`, `OPT(E, v) ≤ α · E_{P∼μ}[value of max-weight base of P]`
  (the paper's `E(…) ≥ 1/α × OPT`, written multiplicatively). -/
def IsPartitionScheme (E : Finset (Sym2 V)) (μ : PMF (Finset (Finset (Sym2 V)))) (α : ℝ) :
    Prop :=
  (∀ P ∈ μ.support, IsPartitionOf E P ∧ ∀ S : Finset (Sym2 V), IsPartIndep P S → IsAcyclicSet S) ∧
    ∀ v : Sym2 V → ℝ, (∀ e, 0 ≤ v e) →
      OPT E v ≤ α * pmfExp μ fun P => partitionValue P v

/-- Definition 5.1: the graphic matroid on `E` satisfies an `α`-partition property if some
random partition `μ` is an `α`-partition scheme for it. -/
def SatisfiesPartitionProperty (E : Finset (Sym2 V)) (α : ℝ) : Prop :=
  ∃ μ : PMF (Finset (Finset (Sym2 V))), IsPartitionScheme E μ α

end SecretaryWD.Graphic
