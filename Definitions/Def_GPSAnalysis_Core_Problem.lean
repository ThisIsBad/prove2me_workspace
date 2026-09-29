import Mathlib

open Matrix

namespace GPSAnalysis.Core

/-- The feasible region of problem (1.1) of Audet–Dennis (2003):
`Ω = {x ∈ ℝⁿ : ℓ ≤ A x ≤ u}` with `ℓ, u ∈ (ℝ ∪ {±∞})ᵐ`, compared componentwise in `EReal`.
When `m = 0`, `Ω = ℝⁿ`. -/
def feasibleSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (lo up : Fin m → EReal) :
    Set (Fin n → ℝ) :=
  {x | ∀ i, lo i ≤ (((A *ᵥ x) i : ℝ) : EReal) ∧ (((A *ᵥ x) i : ℝ) : EReal) ≤ up i}

/-- The barrier function `f_Ω = f + ψ_Ω` (p. 890): `f_Ω(x) = f(x)` if `x ∈ Ω`, and `+∞` otherwise. -/
noncomputable def barrier {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) (Ω : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : WithTop ℝ := by
  classical
  exact if x ∈ Ω then f x else ⊤

/-- Assumption A2 (p. 894): every entry of the constraint matrix is rational. -/
def IsRationalMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, ∃ q : ℚ, A i j = (q : ℝ)

end GPSAnalysis.Core
