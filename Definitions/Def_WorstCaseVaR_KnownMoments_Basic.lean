import Mathlib

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

/-- The loss set `𝒮 = {x | γ ≤ -xᵀw}` of El Ghaoui–Oks–Oustry (2003), Eq. (13), p. 546:
the returns `x ∈ ℝⁿ` for which the portfolio `w` loses at least `γ`, i.e. `γ ≤ -r(w, x)` with
`r(w, x) = wᵀx`. -/
def lossSet {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (γ : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | γ ≤ -⟪w, x⟫_ℝ}

/-- `P` is a probability distribution on `ℝⁿ` (a Borel probability measure, not necessarily with a
density) with mean vector `xhat` and covariance matrix `Γ` (Theorem 1, p. 545: the class `𝒫`).
Square-integrability of every coordinate is part of the predicate, so that the mean and the
covariance are genuine (finite) moments. -/
structure HasMeanCov {n : ℕ} (P : Measure (EuclideanSpace ℝ (Fin n)))
    (xhat : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  memLp_two : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 P
  mean_eq : ∀ i : Fin n, ∫ x, x i ∂P = xhat i
  cov_eq : ∀ i j : Fin n, ∫ x, (x i - xhat i) * (x j - xhat j) ∂P = Γ i j

/-- `κ(ε) = √((1 - ε)/ε)`, Eq. (8), p. 545. -/
noncomputable def kappa (ε : ℝ) : ℝ :=
  Real.sqrt ((1 - ε) / ε)

/-- The bordered symmetric block matrix `[[A, v], [vᵀ, c]]` of size `(n+1) × (n+1)`, indexed by
`Fin n ⊕ Fin 1`: upper-left block `A`, column `v`, row `vᵀ`, scalar corner `c`. -/
def bordered {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (c : ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks A (Matrix.of fun i _ => v i) (Matrix.of fun _ j => v j) (Matrix.of fun _ _ => c)

/-- `S = Γ + x̂x̂ᵀ`, Eq. (6), p. 545. -/
def momentS {n : ℕ} (xhat : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Γ + Matrix.vecMulVec ⇑xhat ⇑xhat

/-- The second-moment matrix `Σ = [[S, x̂], [x̂ᵀ, 1]]`, `S = Γ + x̂x̂ᵀ`, Eq. (6), p. 545,
defined directly from the mean `x̂` and the covariance `Γ`. -/
def secondMomentMatrix {n : ℕ} (xhat : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  bordered (momentS xhat Γ) ⇑xhat 1

/-- The lifted vector `[x; 1] ∈ ℝ^{n+1}`. -/
def liftVec {n : ℕ} (x : Fin n → ℝ) : Fin n ⊕ Fin 1 → ℝ :=
  Sum.elim x (fun _ => 1)

/-- The quadratic function `l(x) = [xᵀ 1] M [xᵀ 1]ᵀ`, Eq. (15), p. 546. -/
def quadFn {n : ℕ} (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (x : Fin n → ℝ) : ℝ :=
  liftVec x ⬝ᵥ (M *ᵥ liftVec x)

end WorstCaseVaR.KnownMoments
