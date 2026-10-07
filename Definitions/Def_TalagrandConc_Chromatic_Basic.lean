import Mathlib

namespace TalagrandConc.Chromatic

open MeasureTheory
open scoped Classical

/-- The set `E₀ = {(i, j) ; i < j}` of possible edges on the vertex set `V = {0, …, n-1}`
(the paper's `{1, …, n}`, shifted to 0-based indices). -/
abbrev EdgeSlot (n : ℕ) : Type := {e : Fin n × Fin n // e.1 < e.2}

/-- The probability measure on `Ω = {0, 1}` (here `Bool`, `true = 1`) giving weight `p` to `1`
and `1 - p` to `0`. It is a probability measure when `0 ≤ p ≤ 1`. -/
noncomputable def coin (p : ℝ) : Measure Bool :=
  Real.toNNReal p • Measure.dirac true + Real.toNNReal (1 - p) • Measure.dirac false

/-- The product probability `P` on `Ω^{E₀}`: one independent `coin p` per possible edge.
Under `P`, the graph `graphOf x` is the random graph `G(n, p)`. -/
noncomputable def gnp (n : ℕ) (p : ℝ) : Measure (EdgeSlot n → Bool) :=
  Measure.pi (fun _ : EdgeSlot n => coin p)

/-- The graph `G(x)` of an edge configuration `x ∈ {0,1}^{E₀}`: for `i < j`, `(i, j) ∈ G(x)` iff
`x_{(i,j)} = 1`. -/
def graphOf {n : ℕ} (x : EdgeSlot n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => ∃ h : i < j, x ⟨(i, j), h⟩ = true

/-- `χ(G, A)`: the chromatic number of the subgraph of `G` induced on `A`, i.e. the smallest
number of independent sets of `G` covering `A`. `χ(G, ∅) = 0`. -/
noncomputable def chiSet {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℕ∞ :=
  (G.induce (A : Set (Fin n))).chromaticNumber

/-- `χ(G, m) = inf {χ(G, A) ; card A = m}`, computed in `ℕ∞`; it is `⊤` (`+∞`) when `m > n`
(empty infimum). -/
noncomputable def chiM {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : ℕ∞ :=
  ⨅ (A : Finset (Fin n)) (_ : A.card = m), chiSet G A

/-- `χ(G, m)` viewed in `WithTop ℤ` (same value, `⊤ ↦ ⊤`), so that it can be compared with
integers `a`, `a - k`. -/
noncomputable def chiMZ {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : WithTop ℤ :=
  WithTop.map (fun c : ℕ => (c : ℤ)) (chiM G m)

/-- `sup {χ(G, F) ; F ⊂ V, card F ≤ s}` in `ℕ∞` (the family always contains `F = ∅` when
`0 ≤ s`). -/
noncomputable def localSup {n : ℕ} (G : SimpleGraph (Fin n)) (s : ℝ) : ℕ∞ :=
  ⨆ (F : Finset (Fin n)) (_ : (F.card : ℝ) ≤ s), chiSet G F

/-- The vertex-exposure product `Ω' = ∏_j Ω_j` with `Ω_j = {0,1}^{j}` for the 0-based vertex `j`
(the paper's `Ω_j = {0,1}^{j-1}` for `1 ≤ j ≤ n`): the coordinate `ω_j = (ω_{i,j})_{i<j}` records
the edges from `j` to the earlier vertices. The coordinate of vertex `0` is the one-point space
`{0,1}^0`. -/
abbrev VxSpace (n : ℕ) : Type := (j : Fin n) → (Fin j.val → Bool)

/-- The graph `G(ω)` of `ω ∈ Ω'`: for `i < j`, `(i, j) ∈ G(ω)` iff `ω_{i,j} = 1`. -/
def vxGraph {n : ℕ} (ω : VxSpace n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => ∃ h : i < j, ω j ⟨i.val, h⟩ = true

/-- The set `A ⊂ Ω'` of the proof of Theorem 9.1 (p. 163): the `ω` with `χ(G(ω), m) ≥ a` and
`sup {χ(G(ω), F) : card F ≤ t√m} ≤ k`. -/
noncomputable def setA (n m k : ℕ) (t : ℝ) (a : ℤ) : Set (VxSpace n) :=
  {ω | (a : WithTop ℤ) ≤ chiMZ (vxGraph ω) m ∧ localSup (vxGraph ω) (t * Real.sqrt m) ≤ k}

/-- The set `B` of Eq. (9.3): the `ω ∈ Ω'` such that for every family of nonnegative weights
`(α_j)` there is `ω' ∈ A` with `∑_j α_j 1_{ω_j ≠ ω'_j} ≤ t √(∑_j α_j²)`. -/
def setB {n : ℕ} (A : Set (VxSpace n)) (t : ℝ) : Set (VxSpace n) :=
  {ω | ∀ α : Fin n → ℝ, (∀ j, 0 ≤ α j) →
    ∃ ω' ∈ A, (∑ j, if ω j ≠ ω' j then α j else 0) ≤ t * Real.sqrt (∑ j, α j ^ 2)}

/-- `N(G, e)` for `e = (i, j) ∈ E₀`: the number of independent sets of `G` of size `r` that
contain both `i` and `j`. -/
noncomputable def indepCount {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (e : EdgeSlot n) : ℕ :=
  ((G.indepSetFinset r).filter (fun s => e.1.1 ∈ s ∧ e.1.2 ∈ s)).card

end TalagrandConc.Chromatic
