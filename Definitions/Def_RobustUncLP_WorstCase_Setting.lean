import Mathlib
open Matrix

namespace RobustUncLP.WorstCase

/-- Feasible set of the instance (6) of the uncertain LP with constraint matrix `A`:
`{x | Ax ≥ 0, fᵀx = 1}` (componentwise order on `Fin m → ℝ`). -/
def instFeas {m n : ℕ} (f : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | 0 ≤ A *ᵥ x ∧ f ⬝ᵥ x = 1}

/-- The robust feasible set `G_𝒰 = {x | Ax ≥ 0 ∀ A ∈ 𝒰; fᵀx = 1}` of (7)/(12):
the feasible set of the robust counterpart `(P_𝒰)`. -/
def robustFeas {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) (f : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | (∀ A ∈ U, 0 ≤ A *ᵥ x) ∧ f ⬝ᵥ x = 1}

/-- `𝒰_i`: the projection of `𝒰` onto the data of the `i`-th constraint, i.e. the set of
all realizations of the `i`-th row (a row is written as a vector of `ℝⁿ`). -/
def rowProj {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) (i : Fin m) : Set (Fin n → ℝ) :=
  (fun A : Matrix (Fin m) (Fin n) ℝ => A i) '' U

/-- `𝒰̂ = 𝒰₁ × ⋯ × 𝒰_m`: the direct product of the row projections of `𝒰`. -/
def rowProduct {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) :
    Set (Matrix (Fin m) (Fin n) ℝ) :=
  {A | ∀ i, A i ∈ rowProj U i}

/-- Constraint-wise uncertainty: `𝒰 = 𝒰₁ × ⋯ × 𝒰_m`. Since `𝒰 ⊆ 𝒰̂` always holds, this is
stated as the inclusion `𝒰̂ ⊆ 𝒰`. -/
def IsConstraintWise {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) : Prop :=
  rowProduct U ⊆ U

/-- Boundedness Assumption (§2.2): there is a convex compact `Q ⊆ ℝⁿ` containing the
feasible set of every instance `A ∈ 𝒰`. -/
def BoundednessAssumption {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) (f : Fin n → ℝ) :
    Prop :=
  ∃ Q : Set (Fin n → ℝ), Convex ℝ Q ∧ IsCompact Q ∧ ∀ A ∈ U, instFeas f A ⊆ Q

/-- Feasibility in the §2.2 example (printed form, variables `x = (x₁, x₂)` as `x 0, x 1`):
`a₁₁x₁ + x₂ ≥ 1`, `x₁ + a₂₂x₂ ≥ 1`, `x₁ + x₂ = 1`, `x₁, x₂ ≥ 0`. -/
def gapFeas (a11 a22 : ℝ) (x : Fin 2 → ℝ) : Prop :=
  1 ≤ a11 * x 0 + x 1 ∧ 1 ≤ x 0 + a22 * x 1 ∧ x 0 + x 1 = 1 ∧ 0 ≤ x 0 ∧ 0 ≤ x 1

end RobustUncLP.WorstCase
