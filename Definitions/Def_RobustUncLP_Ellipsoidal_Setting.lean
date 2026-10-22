import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting

namespace RobustUncLP.Ellipsoidal

open Matrix

/-- The Euclidean norm `‖v‖ = √(vᵀv)` of `v ∈ ℝ^M`. Written out because the norm Mathlib puts
on `Fin M → ℝ` is the sup norm; every `‖·‖` of Ben-Tal & Nemirovski (1999) is Euclidean
(p. 7, after (13)). -/
noncomputable def euclidNorm {M : ℕ} (v : Fin M → ℝ) : ℝ :=
  Real.sqrt (∑ j, v j ^ 2)

/-- Feasible set of one instance of the uncertain LP (6), p. 3:
`{x | Ax ≥ 0, fᵀx = 1}` for the data matrix `A`. -/
def instFeas {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (f : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ (A *ᵥ x) i) ∧ f ⬝ᵥ x = 1}

/-- A set of `m × n` matrices is bounded (condition B, p. 8): all entries of all its members
are bounded by one constant. -/
def UncBounded {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) : Prop :=
  ∃ C : ℝ, ∀ A ∈ U, ∀ a b, |A a b| ≤ C

/-- The data of an ellipsoidal uncertainty (15), p. 8: for `ℓ = 0, …, k` an affine map
`Π_ℓ : ℝ^{L_ℓ} → ℝ^{m×n}`, `Π_ℓ(u) = P0 ℓ + ∑_j u_j • P ℓ j`, and an `M_ℓ × L_ℓ` matrix `Q_ℓ`. -/
structure EllipsoidalData (m n k : ℕ) where
  /-- `L ℓ`: dimension of the parameter space of `Π_ℓ`. -/
  L : Fin (k + 1) → ℕ
  /-- `M ℓ`: number of rows of `Q_ℓ`. -/
  M : Fin (k + 1) → ℕ
  /-- Constant term of the affine map `Π_ℓ`. -/
  P0 : Fin (k + 1) → Matrix (Fin m) (Fin n) ℝ
  /-- Coefficient matrices of the affine map `Π_ℓ`. -/
  P : (ℓ : Fin (k + 1)) → Fin (L ℓ) → Matrix (Fin m) (Fin n) ℝ
  /-- The matrix `Q_ℓ`. -/
  Q : (ℓ : Fin (k + 1)) → Matrix (Fin (M ℓ)) (Fin (L ℓ)) ℝ

namespace EllipsoidalData

variable {m n k : ℕ}

/-- The affine map `Π_ℓ(u) = P0_ℓ + ∑_j u_j P_ℓ^j`. -/
def Pi (D : EllipsoidalData m n k) (ℓ : Fin (k + 1)) (u : Fin (D.L ℓ) → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  D.P0 ℓ + ∑ j, u j • D.P ℓ j

/-- The ellipsoid (14), p. 7: `U(Π_ℓ, Q_ℓ) = {Π_ℓ(u) | ‖Q_ℓ u‖ ≤ 1}`. -/
def ellipsoid (D : EllipsoidalData m n k) (ℓ : Fin (k + 1)) :
    Set (Matrix (Fin m) (Fin n) ℝ) :=
  {A | ∃ u, A = D.Pi ℓ u ∧ euclidNorm (D.Q ℓ *ᵥ u) ≤ 1}

/-- Condition A, (15), p. 8: `𝒰 = ⋂_{ℓ=0}^k U(Π_ℓ, Q_ℓ)`. -/
def uncSet (D : EllipsoidalData m n k) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  ⋂ ℓ, D.ellipsoid ℓ

/-- Condition C ("Slater condition"), p. 8, read for every `ℓ = 0, …, k`: one matrix `A` is
`Π_ℓ(u^ℓ)` with `‖Q_ℓ u^ℓ‖ < 1` for every `ℓ`. -/
def SlaterC (D : EllipsoidalData m n k) : Prop :=
  ∃ A : Matrix (Fin m) (Fin n) ℝ, ∀ ℓ, ∃ u, A = D.Pi ℓ u ∧ euclidNorm (D.Q ℓ *ᵥ u) < 1

end EllipsoidalData

end RobustUncLP.Ellipsoidal
