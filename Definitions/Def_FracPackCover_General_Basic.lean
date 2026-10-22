import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic

namespace FracPackCover.General

/-!
# The GENERAL problem `∃? x ∈ P, Ax ≤ b` (Plotkin–Shmoys–Tardos, Cornell ORIE TR 999, §4, pp. 23–25)

Data: an arbitrary real `m × n` matrix `A`, an arbitrary vector `b ∈ ℝ^m`, a positive vector
`d ∈ ℝ^m` (the error scale), and a convex set `P ⊆ ℝ^n`. Constraints are indexed by `Fin m`,
coordinates by `Fin n`. No sign hypothesis is placed on `A`, `b` or `P`.
-/

/-- `λ(x) = max_i (a_i x − b_i)/d_i`, the least `λ` with `Ax ≤ b + λd` (p. 24). It may be
negative. Defined for `m ≥ 1` (a nonempty maximum). -/
noncomputable def lam {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (FracPackCover.Covering.rowVal A x i - b i) / d i)

/-- The Lagrangean value `y^t(Ax − b) = ∑_i y_i (a_i x − b_i)`. -/
def lagr {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (y : Fin m → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, y i * (FracPackCover.Covering.rowVal A x i - b i)

/-- The dual solution corresponding to `x` (p. 25): `y_i = (1/d_i) e^{α(a_i x − b_i)/d_i}`. -/
noncomputable def dualVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (α : ℝ)
    (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => (1 / d i) * Real.exp (α * (FracPackCover.Covering.rowVal A x i - b i) / d i)

/-- The potential function `Φ = y^t d = ∑_i e^{α(a_i x − b_i)/d_i}` (p. 26). -/
noncomputable def potential {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (α : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, Real.exp (α * (FracPackCover.Covering.rowVal A x i - b i) / d i)

/-- Relaxed optimality condition (𝒢1) (p. 24): `λ y^t d ≤ 4 y^t(Ax − b)`. -/
def G1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (x : Fin n → ℝ)
    (lamv : ℝ) (y : Fin m → ℝ) : Prop :=
  lamv * ∑ i, y i * d i ≤ 4 * lagr A b y x

/-- Relaxed optimality condition (𝒢2) (p. 24): `y^t(Ax − b) − C ≤ (λ/5) y^t d`, where `C` is the
value `C_𝒢(y) = min(y^t A x' − y^t b : x' ∈ P)` (supplied as a number; every use below passes
the value at an exact minimizer). -/
def G2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (x : Fin n → ℝ)
    (lamv : ℝ) (y : Fin m → ℝ) (C : ℝ) : Prop :=
  lagr A b y x - C ≤ lamv / 5 * ∑ i, y i * d i

/-- Subroutine (10) (p. 23): for every `y ≥ 0`, `orc y ∈ P` minimizes `c x = y^t A x` over `P`. -/
def IsMinOracle {m n : ℕ} (P : Set (Fin n → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ y : Fin m → ℝ, 0 ≤ y →
    orc y ∈ P ∧ ∀ x' ∈ P, ∑ i, y i * FracPackCover.Covering.rowVal A (orc y) i ≤ ∑ i, y i * FracPackCover.Covering.rowVal A x' i

/-- `ρ` is an upper bound on the width `max_i max_{x∈P} |a_i x − b_i|/d_i` (p. 23):
`|a_i x − b_i| ≤ ρ d_i` for every `x ∈ P` and every row `i`. -/
def WidthBound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (ρ : ℝ) : Prop :=
  ∀ x ∈ P, ∀ i, |FracPackCover.Covering.rowVal A x i - b i| ≤ ρ * d i

end FracPackCover.General
