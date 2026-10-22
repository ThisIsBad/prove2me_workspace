import Mathlib

namespace FracPackCover.Covering

/-! # The fractional covering problem (Plotkin, Shmoys, Tardos, Cornell ORIE TR 999, §3, pp. 16–17)

COVERING: `∃? x ∈ P` such that `A x ≥ b`, where `A` is a nonnegative `m × n` matrix, `b > 0`, and
`P` is a convex set in the nonnegative orthant of `ℝⁿ`. Rows are indexed by `Fin m`, coordinates by
`Fin n`. -/

/-- The standing assumptions of §3 (p. 16): `A ≥ 0` entrywise, `b > 0`, `P` convex, nonempty and
contained in the nonnegative orthant. -/
def IsCoveringData {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ (∀ i, 0 < b i) ∧ Convex ℝ P ∧ P.Nonempty ∧ (∀ x ∈ P, ∀ j, 0 ≤ x j)

/-- The row value `a_i x = ∑_j A_{ij} x_j`. -/
def rowVal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  ∑ j, A i j * x j

/-- `ρ` is an upper bound on the width `max_i max_{x ∈ P} a_i x / b_i` (p. 16): `ρ > 0` and
`a_i x ≤ ρ b_i` for every `x ∈ P` and every row `i`. -/
def WidthBound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ x ∈ P, ∀ i, rowVal A x i ≤ ρ * b i

/-- `λ(x) = min_i a_i x / b_i`, the maximum `λ` with `A x ≥ λ b` (p. 17, the notation `(x, λ)`). -/
noncomputable def lam {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => rowVal A x i / b i)

/-- `yᵗ A x = ∑_i y_i a_i x`. -/
def yAx {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, y i * rowVal A x i

/-- `yᵗ b = ∑_i y_i b_i`. -/
def ytb {m : ℕ} (b : Fin m → ℝ) (y : Fin m → ℝ) : ℝ :=
  ∑ i, y i * b i

/-- Subroutine (7) (p. 17) as an exact **maximizer**: for every `y ≥ 0`, `orc y ∈ P` and
`orc y` maximizes `c x = yᵗ A x` over `P`, so `C_𝒞(y) = yᵗ A (orc y)`. Box (7) prints `min`, but
`C_𝒞(y)` (p. 17), Figure 3, Lemma 3.3 and Lemma 3.6 all maximize; this is the reading adopted. -/
def IsMaxOracle {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (P : Set (Fin n → ℝ))
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ y : Fin m → ℝ, (∀ i, 0 ≤ y i) → orc y ∈ P ∧ ∀ x ∈ P, yAx A y x ≤ yAx A y (orc y)

/-- Relaxed optimality condition (𝒞1) (p. 17): `(1 + ε) λ yᵗb ≥ yᵗ A x`. -/
def C1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (ε l : ℝ) (y : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  yAx A y x ≤ (1 + ε) * l * ytb b y

/-- Relaxed optimality condition (𝒞2) (p. 17): `C_𝒞(y) − yᵗ A x ≤ ε (C_𝒞(y) + yᵗb)`, where the value
`C = C_𝒞(y)` is passed explicitly. -/
def C2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (ε : ℝ) (y : Fin m → ℝ)
    (x : Fin n → ℝ) (C : ℝ) : Prop :=
  C - yAx A y x ≤ ε * (C + ytb b y)

/-- The dual solution corresponding to `x` (p. 18): `y_i = (1/b_i) e^{−α a_i x / b_i}`. -/
noncomputable def dualY {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (α : ℝ)
    (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => (1 / b i) * Real.exp (-(α * rowVal A x i / b i))

/-- The potential function `Φ = yᵗb = ∑_i e^{−α a_i x / b_i}` (p. 18) of `x`, with `y` the dual
solution corresponding to `x`. -/
noncomputable def potential {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (α : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ytb b (dualY A b α x)

end FracPackCover.Covering
