import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Kearns and Vazirani, *An Introduction to Computational Learning Theory*, Chapter 1:
# the Probably Approximately Correct learning model

Kearns and Vazirani, *An Introduction to Computational Learning Theory*, MIT Press 1994,
doi:10.7551/mitpress/3897.001.0001, Chapter 1 (pp. 1–30).

**The PAC model (§1.2, Definitions 1–5).** An *instance space* `X`, a *concept* `c : X → {0,1}`
(a subset of `X`), a *concept class* `C`, and a *target distribution* `D` on `X`. The oracle
`EX(c, D)` returns labeled examples `(x, c(x))` with `x ~ D`, independently. The *error* of a
hypothesis `h` is `error(h) = Pr_{x ~ D}[c(x) ≠ h(x)]`. `C` is **PAC learnable** using the
hypothesis class `H` if there is an algorithm `L` such that for every `c ∈ C`, every `D`, and all
`0 < ε, δ < 1/2`, given access to `EX(c, D)` and inputs `ε, δ`, with probability at least `1 − δ`
`L` outputs `h ∈ H` with `error(h) ≤ ε`; *efficiently* PAC learnable if moreover `L` runs in time
polynomial in `1/ε`, `1/δ`, `n` and `size(c)`.

**This module** states the model in the *sample-complexity* sense: a learning algorithm is a
function from labeled samples of `m` examples to hypotheses, and the guarantee is that the
sample law of the failure set `{S : error(L(S)) > ε}` is at most `δ`. Running time is not
modelled. The classes of Chapter 1 are built explicitly: conjunctions of boolean literals over
`{0,1}^n` with the *elimination algorithm* of §1.3 (start from all `2n` literals, delete every
literal contradicted by a positive example), axis-aligned rectangles in the plane with the
*tightest-fit* algorithm of §1.1, and 3-CNF formulae learned through the expansion
`y_{u,v,w} = u ∨ v ∨ w` of §1.5.
-/

open MeasureTheory

namespace ComputationalLearning

/-! ### The PAC framework in the sample-complexity sense -/

section PAC

variable {X : Type*} [MeasurableSpace X]

/-- `error(h) = Pr_{x ~ D}[c(x) ≠ h(x)]` (p. 9), the error of the hypothesis `h` with respect to the
target concept `c` and the distribution `D`. -/
noncomputable def errorOf (D : Measure X) (c h : X → Bool) : ℝ :=
  (D {x | h x ≠ c x}).toReal

/-- The law of one labeled example `(x, c(x))` returned by the oracle `EX(c, D)`. -/
noncomputable def exampleLaw (D : Measure X) (c : X → Bool) : Measure (X × Bool) :=
  D.map (fun x ↦ (x, c x))

/-- The law of a sample of `m` independent labeled examples from `EX(c, D)`. -/
noncomputable def sampleLaw (D : Measure X) (c : X → Bool) (m : ℕ) :
    Measure (Fin m → X × Bool) :=
  Measure.pi (fun _ ↦ exampleLaw D c)

/-- The sample `S` is labeled by the concept `c`: every example is `(x, c(x))`. -/
def IsLabeledBy {m : ℕ} (c : X → Bool) (S : Fin m → X × Bool) : Prop :=
  ∀ i, (S i).2 = c (S i).1

/-- `h` is **consistent** with the labeled sample `S` (Definition 3, p. 19): `h(xᵢ) = bᵢ` for all
`i`. -/
def IsConsistent {m : ℕ} (h : X → Bool) (S : Fin m → X × Bool) : Prop :=
  ∀ i, h (S i).1 = (S i).2

/-- The `(ε, δ)` PAC guarantee of the learning algorithm `L` on samples of size `m` for the
concept class `C` (Definition 1, p. 10, sample-complexity sense): for every measurable target
concept `c ∈ C` and every target distribution `D`, the probability (outer measure under the
sample law) that `L`'s hypothesis has error greater than `ε` is at most `δ`. -/
def IsPACGuarantee (C : Set (X → Bool)) (m : ℕ) (L : (Fin m → X × Bool) → X → Bool)
    (ε δ : ℝ) : Prop :=
  ∀ c ∈ C, Measurable c → ∀ D : Measure X, IsProbabilityMeasure D →
    sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal δ

/-- `C` is **PAC learnable using `H`** (Definitions 1 and 4, pp. 10 and 25, sample-complexity
sense): for all `0 < ε, δ < 1/2` there are a sample size `m` and an algorithm `L` outputting
hypotheses in `H` with the `(ε, δ)` guarantee on `C`. -/
def PACLearnable (C H : Set (X → Bool)) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 / 2 →
    ∃ (m : ℕ) (L : (Fin m → X × Bool) → X → Bool), (∀ S, L S ∈ H) ∧ IsPACGuarantee C m L ε δ

end PAC

/-! ### Boolean conjunctions and the elimination algorithm (§1.3) -/

section Cube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The boolean cube over the index type `ι` (`{0,1}^n` for `ι = Fin n`): an assignment to the
variables `xᵢ`. -/
abbrev Cube (ι : Type*) := ι → Bool

/-- A literal `(i, b)`: the variable `xᵢ` if `b = true`, its negation if `b = false`; it holds in
`a` iff `a i = b`. -/
abbrev Literal (ι : Type*) := ι × Bool

/-- A conjunction of literals, as the finite set of its literals; its size is its cardinality. -/
abbrev Conjunction (ι : Type*) := Finset (ι × Bool)

/-- The concept represented by a conjunction: `a` is a positive example iff every literal holds. -/
def evalConj (T : Conjunction ι) (a : Cube ι) : Bool :=
  decide (∀ l ∈ T, a l.1 = l.2)

/-- The representation class of conjunctions of boolean literals over `ι`. -/
def conjunctionClass (ι : Type*) [Fintype ι] [DecidableEq ι] : Set (Cube ι → Bool) :=
  {h | ∃ T : Conjunction ι, h = evalConj T}

/-- The **elimination algorithm** for conjunctions (§1.3, p. 16): start from the conjunction of
all `2n` literals and delete every literal that is contradicted by some positive example of the
sample (negative examples are ignored). -/
def eliminate {m : ℕ} (S : Fin m → Cube ι × Bool) : Conjunction ι :=
  Finset.univ.filter (fun l : ι × Bool ↦ ∀ j, (S j).2 = true → (S j).1 l.1 = l.2)

end Cube

/-! ### Axis-aligned rectangles and the tightest fit (§1.1) -/

section Rectangles

/-- The axis-aligned rectangle `[a₁, b₁] × [a₂, b₂]` in the plane, as a concept (empty when
`a₁ > b₁` or `a₂ > b₂`). -/
noncomputable def rectConcept (a b : ℝ × ℝ) : ℝ × ℝ → Bool :=
  fun p ↦ decide (a.1 ≤ p.1 ∧ p.1 ≤ b.1 ∧ a.2 ≤ p.2 ∧ p.2 ≤ b.2)

/-- The concept class of axis-aligned rectangles over the Euclidean plane. -/
def rectangleClass : Set (ℝ × ℝ → Bool) :=
  {h | ∃ a b : ℝ × ℝ, h = rectConcept a b}

/-- The **tightest-fit** algorithm (§1.1, p. 3): the smallest axis-aligned rectangle containing
all the positive examples of the sample, the empty concept if there are none. -/
noncomputable def tightestFit {m : ℕ} (S : Fin m → (ℝ × ℝ) × Bool) : ℝ × ℝ → Bool :=
  if hJ : (Finset.univ.filter (fun j : Fin m ↦ (S j).2 = true)).Nonempty then
    rectConcept
      ((Finset.univ.filter (fun j : Fin m ↦ (S j).2 = true)).inf' hJ (fun j ↦ (S j).1.1),
        (Finset.univ.filter (fun j : Fin m ↦ (S j).2 = true)).inf' hJ (fun j ↦ (S j).1.2))
      ((Finset.univ.filter (fun j : Fin m ↦ (S j).2 = true)).sup' hJ (fun j ↦ (S j).1.1),
        (Finset.univ.filter (fun j : Fin m ↦ (S j).2 = true)).sup' hJ (fun j ↦ (S j).1.2))
  else fun _ ↦ false

end Rectangles

/-! ### 3-CNF formulae and the expansion of §1.5 -/

section ThreeCNF

variable {n : ℕ}

/-- A clause `u ∨ v ∨ w` of at most three literals over `x₁, …, xₙ` (fewer literals by
repetition). -/
abbrev Clause (n : ℕ) := (Fin n × Bool) × (Fin n × Bool) × (Fin n × Bool)

/-- A 3-CNF formula: a finite conjunction of clauses. -/
abbrev ThreeCNF (n : ℕ) := Finset (Clause n)

/-- The value of the clause `u ∨ v ∨ w` on the assignment `a`. -/
def evalClause (k : Clause n) (a : Cube (Fin n)) : Bool :=
  decide (a k.1.1 = k.1.2 ∨ a k.2.1.1 = k.2.1.2 ∨ a k.2.2.1 = k.2.2.2)

/-- The concept represented by a 3-CNF formula: every clause is satisfied. -/
def evalThreeCNF (F : ThreeCNF n) (a : Cube (Fin n)) : Bool :=
  decide (∀ k ∈ F, evalClause k a = true)

/-- The representation class of 3-CNF formulae over `x₁, …, xₙ`. -/
def threeCNFClass (n : ℕ) : Set (Cube (Fin n) → Bool) :=
  {h | ∃ F : ThreeCNF n, h = evalThreeCNF F}

/-- The expansion of an assignment `a` to the `(2n)³` new variables `y_{u,v,w} = u ∨ v ∨ w`
(§1.5, p. 23). -/
def expand (a : Cube (Fin n)) : Cube (Clause n) :=
  fun k ↦ evalClause k a

/-- The expansion of a labeled sample: each `(a, b)` becomes `(a', b)`. -/
def expandSample {m : ℕ} (S : Fin m → Cube (Fin n) × Bool) : Fin m → Cube (Clause n) × Bool :=
  fun j ↦ (expand (S j).1, (S j).2)

/-- The 3-CNF learning algorithm of §1.5: run the elimination algorithm on the expanded sample
and read the resulting conjunction over the `y_{u,v,w}` back on the original variables. -/
def learnThreeCNF {m : ℕ} (S : Fin m → Cube (Fin n) × Bool) : Cube (Fin n) → Bool :=
  fun a ↦ evalConj (eliminate (expandSample S)) (expand a)

end ThreeCNF

end ComputationalLearning
