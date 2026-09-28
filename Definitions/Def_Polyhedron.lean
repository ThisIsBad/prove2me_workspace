import Mathlib.Data.Matrix.Mul
import Mathlib.Data.EReal.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
Core polyhedron / linear-program definitions.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997 — Definition 2.1 (polyhedron, p. 42), §1.1/§2.1
(standard-form polyhedron), Definition 2.2 (bounded, p. 43), and the
infeasible / finite / unbounded optimal-cost trichotomy (p. 67, Table 4.2).

Design (see CLAUDE.md): vectors are `Fin n → ℝ`, constraints via
`Matrix.mulVec`; the optimal cost lives in `EReal` so that `⊤` = infeasible
and `⊥` = unbounded — never an ℝ-valued `sInf` (whose `sInf ∅ = 0` junk
falsifies the book's statements).
-/

open Matrix

namespace LinearOptimization

/-- **B&T Definition 2.1 (p. 42).** The polyhedron in general form determined by a
constraint matrix `A` and right-hand side `b`: the set `{x | Ax ≥ b}`. -/
def polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {x | b ≤ A.mulVec x}

/-- **B&T §2.1 (p. 42).** The polyhedron in standard form: `{x | Ax = b, x ≥ 0}`. -/
def stdPolyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {x | A.mulVec x = b ∧ 0 ≤ x}

/-- **B&T Definition 2.2 (p. 43).** A set is bounded if it is contained in a
box `[-K, K]^n` for some `K`. (Equivalent to Mathlib's `Bornology.IsBounded`;
stated in the book's elementary form.) -/
def IsBoundedSet {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ K : ℝ, ∀ x ∈ S, ∀ i, |x i| ≤ K

/-- The optimal cost of the linear program `minimize c'x subject to x ∈ S`,
valued in `EReal`: `⊤` iff `S = ∅` (infeasible), `⊥` iff the cost is
unbounded below. This total function encodes the book's trichotomy
(B&T p. 67 and Table 4.2, p. 151). -/
noncomputable def lpValue {n : ℕ} (c : Fin n → ℝ) (S : Set (Fin n → ℝ)) : EReal :=
  ⨅ x ∈ S, ((c ⬝ᵥ x : ℝ) : EReal)

/-- `x` is an optimal solution of `minimize c'x over S`. -/
def IsLpOptimal {n : ℕ} (c : Fin n → ℝ) (S : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, c ⬝ᵥ x ≤ c ⬝ᵥ y

end LinearOptimization
