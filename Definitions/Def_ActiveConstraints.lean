import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
Linear constraint systems and active constraints.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §2.2 pp. 47–48: a polyhedron `P ⊆ ℝⁿ` defined in
terms of linear equality and inequality constraints
`aᵢ'x ≥ bᵢ (i ∈ M₁)`, `aᵢ'x ≤ bᵢ (i ∈ M₂)`, `aᵢ'x = bᵢ (i ∈ M₃)`,
and **Definition 2.8 (p. 48)**: if a vector `x*` satisfies `aᵢ'x* = bᵢ` for
some `i` in `M₁`, `M₂`, or `M₃`, the corresponding constraint is *active*
(or *binding*) at `x*`.

Design (see CLAUDE.md): the mixed system is a finite family of tagged
constraints, indexed by an arbitrary `Fintype` so that general-form
(`Ax ≥ b`) and standard-form (`Ax = b, x ≥ 0`) systems are instances of the
same notion — the notions of basic solution (Definition 2.9) are
*representation-dependent*, as the book stresses after Definition 2.9, so
the constraint data (not just the solution set) must be part of the
encoding.
-/

open Matrix

namespace LinearOptimization

/-- The relation carried by one linear constraint: `≥`, `≤`, or `=`
(the book's index sets `M₁`, `M₂`, `M₃`, §2.2 p. 47). -/
inductive ConstraintRel : Type
  | ge : ConstraintRel
  | le : ConstraintRel
  | eq : ConstraintRel
deriving DecidableEq

/-- One linear constraint `a'x ⋈ b` on `ℝⁿ` (B&T §2.2 p. 47: each `aᵢ` is a
vector in `ℝⁿ` and each `bᵢ` is a scalar). -/
structure LinearConstraint (n : ℕ) : Type where
  a : Fin n → ℝ
  b : ℝ
  rel : ConstraintRel

/-- `x` satisfies the constraint `c`. -/
def LinearConstraint.IsSatisfiedAt {n : ℕ} (c : LinearConstraint n)
    (x : Fin n → ℝ) : Prop :=
  match c.rel with
  | .ge => c.b ≤ c.a ⬝ᵥ x
  | .le => c.a ⬝ᵥ x ≤ c.b
  | .eq => c.a ⬝ᵥ x = c.b

/-- **B&T Definition 2.8 (p. 48).** The constraint `c` is *active* (binding)
at `x*` if `a'x* = b` — regardless of whether `c` is an inequality or an
equality constraint. -/
def LinearConstraint.IsActiveAt {n : ℕ} (c : LinearConstraint n)
    (x : Fin n → ℝ) : Prop :=
  c.a ⬝ᵥ x = c.b

/-- The solution set of a finite family of linear constraints — a polyhedron
presented by the mixed system (B&T §2.2 p. 47). -/
def constraintSet {ι : Type} {n : ℕ} (C : ι → LinearConstraint n) :
    Set (Fin n → ℝ) :=
  {x | ∀ i, (C i).IsSatisfiedAt x}

/-- The general-form system `Ax ≥ b` (B&T Definition 2.1) as a constraint
family. -/
def generalFormSystem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Fin m → LinearConstraint n :=
  fun i => ⟨A i, b i, .ge⟩

/-- The standard-form system `Ax = b, x ≥ 0` (B&T §2.1) as a constraint
family: `m` equality constraints followed by the `n` nonnegativity
constraints `xⱼ ≥ 0` (whose constraint vector is the coordinate vector
`eⱼ`). -/
def stdFormSystem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : (Fin m ⊕ Fin n) → LinearConstraint n :=
  fun i => match i with
  | .inl i => ⟨A i, b i, .eq⟩
  | .inr j => ⟨Pi.single j 1, 0, .ge⟩

end LinearOptimization
