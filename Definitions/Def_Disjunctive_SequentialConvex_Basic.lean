import Mathlib

namespace Disjunctive.SequentialConvex

/-- The polyhedron `{x : A x ≥ b}` (restated locally, as in earlier chunks of the series). -/
def Poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, b i ≤ (A.mulVec x) i}

/-- `F₀ := {x ∈ ℝⁿ : Ax ≥ b, x ≥ 0}` (Balas §3.1, p. 42). -/
def F0Set {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, b i ≤ (A.mulVec x) i) ∧ 0 ≤ x}

/-- The halfspaces `{x : dx ≤ d₀}` and `{x : dx ≥ d₀}` (Balas §3.1-3.2, used throughout). -/
def HalfspaceLE {n : ℕ} (d : Fin n → ℝ) (d0 : ℝ) : Set (Fin n → ℝ) := {x | dotProduct d x ≤ d0}

def HalfspaceGE {n : ℕ} (d : Fin n → ℝ) (d0 : ℝ) : Set (Fin n → ℝ) := {x | d0 ≤ dotProduct d x}

/-- The constraint set `F` of a disjunctive program `DP` in conjunctive normal form (Balas §3,
eq. (3.1), p. 42): `F₀` together with, for every `j ∈ S`, a disjunction `⋁_{i ∈ Q_j} (d_i x ≥
d_{i0})`. -/
def DisjunctiveConstraintSet {n : ℕ} {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {S : Type*} [Fintype S] (Qidx : S → Type*) [∀ j, Fintype (Qidx j)]
    (d : (j : S) → Qidx j → Fin n → ℝ) (d0 : (j : S) → Qidx j → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ F0Set A b ∧ ∀ j : S, ∃ i : Qidx j, d0 j i ≤ dotProduct (d j i) x}

/-- `DP` is facial (Balas §3.1, p. 42): every inequality `d_i x ≥ d_{i0}` appearing in a
disjunction of `(3.1)` defines a face of `F₀`. -/
def Facial {n : ℕ} {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {S : Type*}
    [Fintype S] (Qidx : S → Type*) [∀ j, Fintype (Qidx j)] (d : (j : S) → Qidx j → Fin n → ℝ)
    (d0 : (j : S) → Qidx j → ℝ) : Prop :=
  ∀ j : S, ∀ i : Qidx j, IsExtreme ℝ (F0Set A b) (F0Set A b ∩ HalfspaceGE (d j i) (d0 j i))

/-- `D_j := ⋁_{i ∈ Q_j} (d_i x ≥ d_{i0})` (Balas §3.2, p. 46, right before eq. (3.5)). -/
def Dj {n : ℕ} {Qj : Type*} [Fintype Qj] (d : Qj → Fin n → ℝ) (d0 : Qj → ℝ) : Set (Fin n → ℝ) :=
  ⋃ i : Qj, HalfspaceGE (d i) (d0 i)

/-- `D̄_j := ⋁_{i ∈ Q_j} (d_i x ≤ d_{i0})` (Balas §3.2, p. 46, right before Theorem 3.3). -/
def Dbarj {n : ℕ} {Qj : Type*} [Fintype Qj] (d : Qj → Fin n → ℝ) (d0 : Qj → ℝ) :
    Set (Fin n → ℝ) :=
  ⋃ i : Qj, HalfspaceLE (d i) (d0 i)

end Disjunctive.SequentialConvex
