import Mathlib

namespace RobinsonSR.Schur

open scoped RealInnerProductSpace Matrix

/-- The normal cone of a convex set is empty outside the set. -/
def normalCone {ι : Type*} [Fintype ι] (C : Set (EuclideanSpace ℝ ι))
    (x : EuclideanSpace ℝ ι) : Set (EuclideanSpace ℝ ι) :=
  {y | x ∈ C ∧ (∀ c ∈ C, inner ℝ y (c - x) ≤ 0)}

/-- Positive definiteness without a symmetry requirement. -/
def PosDefNS {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ w : ι → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (M *ᵥ w)

/-- Every nonempty principal minor is strictly positive. -/
def IsPMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : Prop :=
  ∀ J : Finset ι, J.Nonempty →
    0 < (M.submatrix (fun i : J => (i : ι)) (fun i : J => (i : ι))).det

/-- Robinson's Schur complement, used when `A₁₁` is nonsingular. -/
noncomputable def schur {r s : ℕ} (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  A₂₂ - A₂₁ * A₁₁⁻¹ * A₁₂

/-- The first block of a vector in `ℝʳ⁺ˢ`. -/
def upperBlock {r s : ℕ} (w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 (fun i => w (Sum.inl i))

/-- The second block of a vector in `ℝʳ⁺ˢ`. -/
def lowerBlock {r s : ℕ} (w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    EuclideanSpace ℝ (Fin s) :=
  WithLp.toLp 2 (fun j => w (Sum.inr j))

/-- The Cartesian product `ℝʳ × K` in Euclidean sum coordinates. -/
def prodSet {r s : ℕ} (K : Set (EuclideanSpace ℝ (Fin s))) :
    Set (EuclideanSpace ℝ (Fin r ⊕ Fin s)) :=
  {w | lowerBlock w ∈ K}

/-- The nonnegative orthant `ℝˢ₊`. -/
def nonnegOrthant (s : ℕ) : Set (EuclideanSpace ℝ (Fin s)) :=
  {w | ∀ j, 0 ≤ w j}

/-- A finite intersection of closed half-spaces. -/
def IsPolyhedral {ι : Type*} [Fintype ι] (C : Set (EuclideanSpace ℝ ι)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → EuclideanSpace ℝ ι) (b : Fin m → ℝ),
    C = {x | ∀ i, inner ℝ (a i) x ≤ b i}

/-- The inverse of `w ↦ Aw + normalCone D w` is an everywhere-defined,
single-valued, globally Lipschitz function. -/
def InvIsLipschitzFunction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (D : Set (EuclideanSpace ℝ ι)) : Prop :=
  ∃ L : ℝ, ∃ σ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι,
    (∀ y, y - A.toEuclideanLin (σ y) ∈ normalCone D (σ y) ∧
      ∀ w, y - A.toEuclideanLin w ∈ normalCone D w → w = σ y) ∧
    ∀ y₁ y₂, ‖σ y₁ - σ y₂‖ ≤ L * ‖y₁ - y₂‖

end RobinsonSR.Schur
