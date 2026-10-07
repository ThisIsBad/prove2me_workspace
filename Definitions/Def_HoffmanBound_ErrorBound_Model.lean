import Mathlib

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 263, (3): a *positive homogeneous function* `F_k` on `k`-space is a real
continuous function with (i) `F_k(x) ≥ 0`, and `F_k(x) = 0` if and only if `x = 0`; and
(ii) `α ≥ 0` implies `F_k(α x) = α F_k(x)`. Nothing else (no triangle inequality, no symmetry,
no convexity) is assumed. -/
def IsPosHomogeneous {k : ℕ} (F : (Fin k → ℝ) → ℝ) : Prop :=
  Continuous F ∧ (∀ x, 0 ≤ F x) ∧ (∀ x, F x = 0 ↔ x = 0) ∧
    ∀ α : ℝ, 0 ≤ α → ∀ x, F (α • x) = α * F x

/-- Hoffman 1952, p. 263, (2): the positive part of a vector, `y⁺ = (y₁⁺, …, y_k⁺)` with
`a⁺ = a` if `a ≥ 0` and `a⁺ = 0` if `a < 0`. -/
def posPartVec {k : ℕ} (y : Fin k → ℝ) : Fin k → ℝ := fun i => max (y i) 0

/-- Hoffman 1952, p. 263, (1): the set `Ω` of solutions of the system `Ax ≤ b`, i.e. of
`A_i · x ≤ b_i` for `i = 1, …, m` (componentwise order). -/
def solutionSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | A *ᵥ x ≤ b}

/-- `y` is a point of `Ω` nearest to `x` in the Euclidean distance: `y ∈ Ω` and
`(x - y)·(x - y) ≤ (x - z)·(x - z)` for every `z ∈ Ω`. -/
def IsNearest {n : ℕ} (Ω : Set (Fin n → ℝ)) (x y : Fin n → ℝ) : Prop :=
  y ∈ Ω ∧ ∀ z ∈ Ω, (x - y) ⬝ᵥ (x - y) ≤ (x - z) ⬝ᵥ (x - z)

/-- The matrix `M` obtained from `A` by substituting `0` for the rows not in `S` (it keeps all
`m` rows). -/
def rowsOn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i => if i ∈ S then A i else 0

/-- The vector `ȳ` obtained from `y` by substituting `0` for the components not in `S`
(Lemma 1; also `b̄` in the proof of the theorem). -/
def restrictVec {m : ℕ} (S : Finset (Fin m)) (y : Fin m → ℝ) : Fin m → ℝ :=
  fun i => if i ∈ S then y i else 0

/-- The set `S` of the half spaces `A_i · z ≤ b_i` whose bounding hyperplane contains `y`,
i.e. the indices with `A_i · y = b_i` (Lemma 2). -/
noncomputable def activeSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => (A *ᵥ y) i = b i

/-- Lemma 3: for `M = rowsOn A S` and the cone `Ω = {z | M z ≤ 0}`, the set `E` of all `x` such
that (i) `x ∉ Ω` and (ii) the origin is the point of `Ω` nearest to `x`. -/
def setE {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) : Set (Fin n → ℝ) :=
  {x | x ∉ solutionSet (rowsOn A S) 0 ∧ IsNearest (solutionSet (rowsOn A S) 0) x 0}

/-- Lemma 4: `K'`, the cone spanned by the row vectors `M_1, …, M_m` of `M = rowsOn A S`, with
the origin deleted: all `x ≠ 0` of the form `λ₁ M₁ + ⋯ + λ_m M_m` with every `λ_i ≥ 0`. -/
def conePrime {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) :
    Set (Fin n → ℝ) :=
  {x | x ≠ 0 ∧ ∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • rowsOn A S i}

end HoffmanBound.ErrorBound
